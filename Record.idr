module Record

import Data.List.Quantifiers
import Effects

%access public export

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

schemaImp : Schema -> (Type -> Type) -> Type
schemaImp s f = Implement (typesOfSchema s) f

data ShowD : (t : Type) -> Type where
	ShowFun : (t -> String) -> ShowD t

%hint
showDAll : Show a => ShowD a
showDAll = ShowFun (show {ty=a})

infixl 10 &
(&) : (Record d -> Record b) -> (Record c -> Record d) -> Record c -> Record b
(&) rf1 rf2 = (\r => rf1 (rf2 r))

infixl 15 ::=
(::=) : {t:Type} -> (s:String) -> (x:t) -> Record xs -> Record ((s,t)::xs)
(::=) s v = RecCons s v

syntax "{" [x] "}" = x RecNil

total
toStringList : Record sch -> {auto ip: schemaImp sch ShowD} -> List (String, String)
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

total
export
-- Prefix, separator, suffix
showRecordCustom : Record sc -> {auto ip: schemaImp sc ShowD} -> ToStringConfig -> String
showRecordCustom {ip} rec conf = let pre = prefix_ conf
                           in let fieldAndVal = betweenFieldAndValue conf
                           in let cons = betweenCons conf
                           in let suffix = suffix conf
                           in let lst = toStringList {ip=ip} rec
                           in pre ++ (joinStr (map (\(k, v) => k ++ fieldAndVal ++ v) lst) cons) ++ suffix


total
export
showRecord : Record sc -> {auto ip: schemaImp sc ShowD} -> String
showRecord {ip} rec = showRecordCustom rec {ip=ip} (MkToStringConfig "{" " ::= " ", " "}")
  
total
export
showRecordAssignment : Record sc -> {auto ip: schemaImp sc ShowD} -> String
showRecordAssignment {ip} rec = showRecordCustom rec {ip=ip} (MkToStringConfig "" " = " ", " "")


