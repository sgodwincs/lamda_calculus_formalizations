namespace Statics

inductive Ty where
  | void
  | sum : Ty → Ty → Ty
  | arrow : Ty → Ty → Ty
  deriving DecidableEq, Repr
