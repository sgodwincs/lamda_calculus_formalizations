namespace Statics

inductive Ty where
  | unit
  | prod : Ty → Ty → Ty
  | void
  | sum : Ty → Ty → Ty
  | arrow : Ty → Ty → Ty
  deriving DecidableEq, Repr
