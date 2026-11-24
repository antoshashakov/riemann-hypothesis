module

public import Formalism.SharedLemmas.HpkSq

/-!
# The long Weyl element is Hermitian

`(Hpk k r)ᴴ = Hpk k r` was proved separately in many modules; this re-exports one proof under a
short import path.
-/

@[expose] public section

namespace Formalism.SharedLemmas

theorem upq_hpk_conjTranspose {k r : ℕ} :
    (PI.UpqRep.Hpk k r).conjTranspose = PI.UpqRep.Hpk k r :=
  PI.HwUniqW.Hpk_conjTranspose

end Formalism.SharedLemmas
