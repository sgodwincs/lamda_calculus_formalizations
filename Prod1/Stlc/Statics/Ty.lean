import Aesop

namespace Statics

inductive Ty where
  | unit
  | prod : Ty → Ty → Ty
  | arrow : Ty → Ty → Ty
  deriving DecidableEq, Repr
