module Record

import Data.List.Quantifiers
import Effects

%access public export
%default total

Schema : Type
Schema = List (String, Type)

typesOfSchema : Schema -> List Type
typesOfSchema sc = map snd sc

data Record : Schema -> Type where
	RecNil : Record Nil
	RecCons : (key:String) -> (val : t) -> Record lst -> Record ((key, t)::lst)

data Useless : Type where I : Useless

typeAtKey : Schema -> String -> Type
typeAtKey Nil _ = Useless
typeAtKey ((k', t)::rest) k = if (k' == k) then t else (typeAtKey rest k)

infixl 10 ..

(..) : Record keyMap -> (k : String) -> typeAtKey keyMap k
(..) RecNil k = I
(..) (RecCons key val rest) k with (key == k)
	| True = val
	| False = rest .. k


data Implement : List Type -> (Type -> Type) -> Type where
	ImpNil : Implement [] f
	ImpCons : f x -> Implement xs f -> Implement (x::xs) f

SchemaImp : Schema -> (Type -> Type) -> Type
SchemaImp s f = Implement (typesOfSchema s) f

-- Data version of show
data ShowD : (t : Type) -> Type where
	ShowFun : (t -> String) -> ShowD t

%hint
showdAll : Show a => ShowD a
showdAll = ShowFun (show {ty=a})


infixl 10 &
(&) : (Record d -> Record b) -> (Record c -> Record d) -> Record c -> Record b
(&) rf1 rf2 = (\r => rf1 (rf2 r))

infixl 15 ::=
(::=) : {t:Type} -> (s:String) -> (x:t) -> Record xs -> Record ((s,t)::xs)
(::=) s v = RecCons s v

syntax "{" [x] "}" = x RecNil

toStringList : Record sch -> {auto ip: SchemaImp sch ShowD} -> List (String, String)
toStringList RecNil = []
toStringList (RecCons k v RecNil) {ip=(ImpCons (ShowFun f) _)} = [(k, f v)]
toStringList (RecCons k v recRest) {ip=(ImpCons (ShowFun f) impRest)} = (k, f v) :: (toStringList {ip=impRest} recRest)

-- Join string using separator
private
joinStr : List String -> (sep : String) -> String
joinStr Nil _ = ""
joinStr [s] _ = s
joinStr (s::rest) sep = s ++ sep ++ (joinStr rest sep)

record ToStringConfig where
  constructor MkToStringConfig
  prefix_ : String
  betweenFieldAndValue : String
  betweenCons : String
  suffix : String

export
-- Prefix, separator, suffix
showRecordCustom : Record sc -> {auto ip: SchemaImp sc ShowD} -> ToStringConfig -> String
showRecordCustom {ip} rec conf = let pre = prefix_ conf
                           in let fieldAndVal = betweenFieldAndValue conf
                           in let cons = betweenCons conf
                           in let suffix = suffix conf
                           in let lst = toStringList {ip=ip} rec
                           in pre ++ (joinStr (map (\(k, v) => k ++ fieldAndVal ++ v) lst) cons) ++ suffix


export
showRecord : Record sc -> {auto ip: SchemaImp sc ShowD} -> String
showRecord {ip} rec = showRecordCustom rec {ip=ip} (MkToStringConfig "{" " ::= " ", " "}")
  
export
showRecordAssignment : Record sc -> {auto ip: SchemaImp sc ShowD} -> String
showRecordAssignment {ip} rec = showRecordCustom rec {ip=ip} (MkToStringConfig "" " = " ", " "")

getKey : SubElem (k, t) sch -> Record sch -> t
getKey Z (RecCons key value _) = value
getKey (S inList) (RecCons _ _ rest) = getKey inList rest

export
getSubRecord : {auto sl : SubList to from} -> Record from -> Record to
getSubRecord {sl=SubNil} _ = RecNil
getSubRecord {sl=InList subElem subList} {to=(key, type)::rest} rec =
  RecCons key (getKey subElem rec) (getSubRecord {sl=subList} rec {to=rest})

public export
replaceType : (sch:Schema) -> SubElem (k, t) sch -> Type -> Schema
replaceType ((k, t)::rest) Z newType = (k, newType)::rest
replaceType (hd::rest) (S se) newType = hd::(replaceType rest se newType)

export
update : {auto se: SubElem (k, t) sch} ->
         (k:String) ->
         (t -> a) ->
         Record sch ->
         Record (replaceType sch se a)
update {se=Z} _ f (RecCons k val rest) = RecCons k (f val) rest
update {se=S sub} k1 f (RecCons k2 val rest) = RecCons k2 val (update {se=sub} k1 f rest)

export
tryUpdate :
  {auto se: SubElem (k, t) sch} ->
  (k:String) ->
  (t -> Maybe a) ->
  Record sch ->
  Maybe (Record (replaceType sch se a))
tryUpdate {se=Z} _ f (RecCons k val rest) = (\upd => RecCons k upd rest) <$> (f val)
tryUpdate {se=S sub} k1 f (RecCons k2 val rest) = (\upd => RecCons k2 val upd) <$> (tryUpdate {se=sub} k1 f rest)

public export
removeKeyInSchema : Schema -> String -> Schema
removeKeyInSchema [] _ = []
removeKeyInSchema ((k1, val)::rest) k2 = if k1 == k2 then rest
                                                     else (k1, val)::(removeKeyInSchema rest k2)
export
removeKey : Record sch -> (key:String) -> Record (removeKeyInSchema sch key)
removeKey RecNil _ = RecNil
removeKey (RecCons k1 val rest) k2 with (k1 == k2)
  | True = rest
  | False = RecCons k1 val (removeKey rest k2)


