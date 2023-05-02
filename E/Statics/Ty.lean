namespace Statics

inductive Ty where
  | number
  | string
  deriving DecidableEq, Repr

instance : ToString Ty where
  toString : Ty → String
  | Ty.number => "number"
  | Ty.string => "string" 
