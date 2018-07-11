{- This Source Code Form is subject to the terms of the Mozilla Public
 - License, v. 2.0. If a copy of the MPL was not distributed with this
 - file, You can obtain one at http://mozilla.org/MPL/2.0/. -}

module Record

import Data.List.Quantifiers
import Effects

%access public export
%default total

||| A schema lists the keys of the record and the corresponding type.
||| Some terminology I use:
||| The first value of the tuple is called a KEY.
||| The second value of the tuple is called a VALUE (corresponding to the KEY).
||| The tuple itself is called a FIELD (of the record).
Schema : Type
Schema = List (String, Type)

||| All the types present in the schema.
typesOfSchema : Schema -> List Type
typesOfSchema = map snd

||| A record is either the empty record,
||| or it is an existing record with another field prepended to it.
data Record : Schema -> Type where
	RecNil : Record Nil
	RecCons : (key:String) -> (val : t) -> Record lst -> Record ((key, t)::lst)

infixl 10 ..

||| Access a value of the record using the key.
||| See comment next to the (&) function for an example.
(..) : Record sch -> (k:String) -> {auto se: SubElem (k, t) sch}  -> t
(..) {se=Z} (RecCons _ val _) _ = val
(..) {se=S seRest} (RecCons _ _ recRest) k = (..) {se=seRest} recRest k

||| All types of a schema implement a certain 
||| interface. 
SchemaImp : Schema -> (Type -> Type) -> Type
SchemaImp s f = All f (typesOfSchema s)

infixl 10 &

||| Syntactic sugar.
||| `let product = ({ "price" ::= 3.0 & "name" ::= "phone" })
||| in putStrLn' (product .. "name")`
(&) : (Record d -> Record b) -> (Record c -> Record d) -> Record c -> Record b
(&) rf1 rf2 = (\r => rf1 (rf2 r))

infixl 15 ::=

||| Syntactic sugar. See comment next to (&) function.
(::=) : {t:Type} -> (s:String) -> (x:t) -> Record xs -> Record ((s,t)::xs)
(::=) s v = RecCons s v

syntax "{" [x] "}" = x RecNil

||| Convert the record to a list of string tuples. The 'ip' argument
||| is neccessary to prove that all type of the schema can be converted.
toStringList : Record sch -> {auto ip: SchemaImp sch Show} -> List (String, String)
toStringList RecNil = []
toStringList (RecCons k v RecNil) {ip=[s]} = [(k, show v)]
toStringList (RecCons k v recRest) {ip=s::showRest} = (k, show v) :: (toStringList {ip=showRest} recRest)

-- Join string using separator
private
joinStr : List String -> (sep : String) -> String
joinStr lst sep = concat $ intersperse sep lst

||| This module contains a few functions to convert records to a string
||| while abstracting over all the separators used. This can be useful
||| to for example convert a record to JSON.
||| To convert a record to the text you would type in using the (::=) and (&) functions
||| you could use `MkToStringConfig "{" " ::= " " & " "}"`
record ToStringConfig where
  constructor MkToStringConfig
  prefix_ : String
  betweenKeyAndValue : String
  betweenCons : String
  suffix : String

||| Convert a record to a string according to the configuration.
export
showRecordCustom : Record sc -> {auto ip: SchemaImp sc Show} -> ToStringConfig -> String
showRecordCustom {ip} rec conf = let pre = prefix_ conf
                           in let fieldAndVal = betweenKeyAndValue conf
                           in let cons = betweenCons conf
                           in let suffix = suffix conf
                           in let lst = toStringList {ip=ip} rec
                           in pre ++ (joinStr (map (\(k, v) => k ++ fieldAndVal ++ v) lst) cons) ++ suffix


-- All Show (typesOfSchema sch) => Show (Record sch) where

||| Convert a record to a string using `MkToStringConfig "{" " ::= " " & " "}"`.
||| This results in the same string you would type in using the (&) and (::=) functions.
export
showRecord : Record sc -> {auto ip: SchemaImp sc Show} -> String
showRecord {ip} rec = showRecordCustom rec {ip=ip} (MkToStringConfig "{" " ::= " " & " "}")

private
getType : SubElem (k, t) sch -> Record sch -> t
getType Z (RecCons key value _) = value
getType (S inList) (RecCons _ _ rest) = getType inList rest

||| We can project a record to a smaller record if the original schema
||| contains all the fields of the smaller record.
export
getSubRecord : {auto sl : SubList to from} -> Record from -> Record to
getSubRecord {sl=SubNil} _ = RecNil
getSubRecord {sl=InList subElem subList} {to=(key, type)::rest} rec =
  RecCons key (getType subElem rec) (getSubRecord {sl=subList} rec {to=rest})

||| Replace the type corresponding to a key.
public export
replaceType : (sch:Schema) -> SubElem (k, t) sch -> Type -> Schema
replaceType ((k, t)::rest) Z newType = (k, newType)::rest
replaceType (hd::rest) (S se) newType = hd::(replaceType rest se newType)

||| Update the value corresponding to a certain key.
||| Todo: maybe add some syntactic sugar?
export
update : {auto se: SubElem (k, t) sch} ->
         (k:String) ->
         (t -> a) ->
         Record sch ->
         Record (replaceType sch se a)
update {se=Z} _ f (RecCons k val rest) = RecCons k (f val) rest
update {se=S sub} k1 f (RecCons k2 val rest) = RecCons k2 val (update {se=sub} k1 f rest)

||| Try to update the value corresponding to a certain key.
||| Return nothing if the conversion failed. 
export
tryUpdate :
  {auto se: SubElem (k, t) sch} ->
  (k:String) ->
  (t -> Maybe a) ->
  Record sch ->
  Maybe (Record (replaceType sch se a))
tryUpdate {se=Z} _ f (RecCons k val rest) = (\upd => RecCons k upd rest) <$> (f val)
tryUpdate {se=S sub} k1 f (RecCons k2 val rest) = (\upd => RecCons k2 val upd) <$> (tryUpdate {se=sub} k1 f rest)

||| Remove the field corresponding to the key from the schema.
public export
removeFieldInSchema : Schema -> String -> Schema
removeFieldInSchema [] _ = []
removeFieldInSchema ((k1, val)::rest) k2 = if k1 == k2 then rest
                                                     else (k1, val)::(removeFieldInSchema rest k2)

||| Remove the field corresponding to the key from the record.
export
removeField : Record sch -> (key:String) -> Record (removeFieldInSchema sch key)
removeField RecNil _ = RecNil
removeField (RecCons k1 val rest) k2 with (k1 == k2)
  | True = rest
  | False = RecCons k1 val (removeField rest k2)


