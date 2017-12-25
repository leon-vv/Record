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

recordToObject : Record sc -> {auto jp : schemaImp sc ToJSD} -> JS_IO (JSValue (JSObject "Object"))
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


%hint
total
ptrFromJSD : FromJSD JSRef
ptrFromJSD  = FromJSFun (\v => Just (unpack v))

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
boolFromJSD : FromJSD Bool
boolFromJSD = FromJSFun f
  where
    f : {jst:JSType} -> JSValue jst -> Maybe Bool
    f {jst=JSBoolean} v = fromFun v
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
objectToRecord : {auto fp : schemaImp schema FromJSD}
    -> JSValue (JSObject "Object")
    -> JS_IO (Maybe (Record schema))
objectToRecord {schema=Nil} _ = pure (Just RecNil)
objectToRecord {schema=((k, t)::rst)} {fp=(ImpCons (FromJSFun f) impRest)} obj =
    do
      maybeRec <- objectToRecord {schema=rst} {fp=impRest} obj
      maybeDPair <- getProperty k obj
      pure (do
        rec <- maybeRec
        (MkDPair t val) <- maybeDPair
        idrisVal <- (f {jst=t} val)
        pure (RecCons k idrisVal rec))

private
log : a -> JS_IO ()
log v = jscall "console.log(%0)" (Ptr -> JS_IO ()) (believe_me v)


%inline
partial
export
objectToRecordUnsafe : {auto fp : schemaImp schema FromJSD} -> JSRef -> JS_IO (Record schema)
objectToRecordUnsafe {fp} ref = do log ref
                                   (JSObject "Object" ** obj) <- pack ref
                                   Just rec <- objectToRecord {fp=fp} obj
                                   log rec
                                   pure rec



