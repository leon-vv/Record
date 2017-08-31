module Record.JS

import Record

import IdrisScript
import IdrisScript.Objects

%access public export
%default total

data ToJSD : Type -> Type where
  ToJSFun : ((from : t) -> JS_IO (JSValue to)) -> ToJSD t

%hint
intToJSD : ToJSD Int
intToJSD = ToJSFun (\i => pure (toJS i {to=JSNumber}))

%hint
doubleToJSD : ToJSD Double
doubleToJSD = ToJSFun (\d => pure (toJS d {to=JSNumber}))

%hint
stringToJSD : ToJSD String
stringToJSD = ToJSFun (\s => pure (toJS s {to=JSString}))

recordToObject : Record sc -> {auto jp : Implement (typesOfSchema sc) ToJSD} -> JS_IO (JSValue (JSObject "Object"))
recordToObject RecNil = Objects.empty
recordToObject (RecCons k v recRest) {jp=(ImpCons (ToJSFun f) impRest)} =
  do obj <- recordToObject recRest {jp=impRest}
     val <- f v
     setProperty k val obj

data FromJSD : Type -> Type where
  FromJSFun : ({jst:JSType} -> JSValue jst -> Maybe to) -> FromJSD to


%hint
total
fromFun : FromJS a b => JSValue a -> Maybe b
fromFun {a} {b} v = Just (fromJS v {from=a} {to=b})


{-
%hint
total
fromJSD : FromJS a b => {jst : JSType} -> {auto eq : a = jst} FromJSD b
fromJSD {a} {b} = FromJSFun (\fromFun {a=a} {b=b}) -}


%hint
total
intFromJSD : FromJSD Int
intFromJSD = FromJSFun f
  where
    f : {jst:JSType} -> JSValue jst -> Maybe Int
    f {jst=JSNumber} v = fromFun v
    f _ = Nothing


%hint
total
stringFromJSD : FromJSD String
stringFromJSD = FromJSFun f
  where
      f : {jst:JSType} -> JSValue jst -> Maybe String
      f {jst=JSString} v = fromFun v
      f _  = Nothing

%hint
total
doubleFromJSD : FromJSD Double
doubleFromJSD = FromJSFun f
  where
      f : {jst:JSType} -> JSValue jst -> Maybe Double
      f {jst=JSNumber} v = fromFun v
      f _  = Nothing

total
objectToRecord : (schema:Schema)
    -> {auto fp : (Implement (typesOfSchema schema) FromJSD)}
    -> (JSValue (JSObject "Object"))
    -> JS_IO (Maybe (Record schema))
objectToRecord Nil _ = pure (Just RecNil)
objectToRecord ((k, t)::rst) {fp=(ImpCons (FromJSFun f) impRest)} obj =
    do
      maybeRec <- objectToRecord rst {fp=impRest} obj
      maybeDPair <- getProperty k obj
      pure (do
        rec <- maybeRec
        (MkDPair t val) <- maybeDPair
        idrisVal <- (f {jst=t} val)
        pure (RecCons k idrisVal rec))

