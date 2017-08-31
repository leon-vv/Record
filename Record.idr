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
showRecord : Record sc -> {auto ip : Implement (typesOfSchema sc) ShowD} -> String
showRecord {ip} rec = "{ " ++ (aux rec ip) ++ " }"
  where
    aux : Record sc -> Implement (typesOfSchema sc) ShowD -> String 
    aux RecNil _ = ""
    aux (RecCons k v RecNil) (ImpCons (ShowFun f) _) = k ++ " ::= " ++ (f v)
    aux (RecCons k v recRst) (ImpCons (ShowFun f) impRest) =
        k ++ " ::= " ++ (f v) ++ ", " ++ (aux recRst impRest)
 
