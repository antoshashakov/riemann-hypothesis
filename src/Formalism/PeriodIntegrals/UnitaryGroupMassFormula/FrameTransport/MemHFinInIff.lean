module

import Supplements.MathlibImports.AnalysisAndTactics
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs

@[expose] public section

noncomputable section

namespace PI.FT

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Matrix
open scoped TensorProduct

section Lin

variable {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {M : ℕ}

variable {J : Matrix (Fin (M + 1)) (Fin (M + 1)) E} {J' : Matrix (Fin M) (Fin M) E}
  {B : Matrix (Fin (M + 1)) (Fin M) E} {x : Fin 1 → Fin (M + 1) → E} {b : E}

end Lin

section Tens

variable {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {M : ℕ}
variable (R : Type) [CommRing R] [Algebra F R]

end Tens

end PI.FT
