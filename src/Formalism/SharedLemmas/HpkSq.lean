module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HighestWeightUniqueness.HpkMulMulHpkApply

/-!
# The long Weyl element squares to one

`Hpk k r * Hpk k r = 1` was proved separately in many modules; this re-exports one proof under a
short import path.
-/

@[expose] public section

namespace Formalism.SharedLemmas

theorem upq_hpk_mul_self {k r : ℕ} : PI.UpqRep.Hpk k r * PI.UpqRep.Hpk k r = 1 :=
  PI.HwUniqW.Hpk_mul_self

end Formalism.SharedLemmas
