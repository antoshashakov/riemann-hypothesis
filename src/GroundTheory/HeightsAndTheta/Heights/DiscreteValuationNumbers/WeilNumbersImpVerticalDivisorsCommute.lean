module

public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Objects
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PCutByFormField
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PIntNumSymm
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

namespace VerticalDivisorsCommuting

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem intNum_snoc {F : Type u} [Field F] (V : Ideal (MRing ι F)) {n : ℕ} (L : Fin n → K → ℤ)
    (b : K → ℤ) :
    intNum F V (Fin.snoc (α := fun _ => K → ℤ) L b) = intNum F V (Matrix.vecCons b L) := by
  rw [← CutByFormField.vecCons_comp_finRotate]
  exact FieldNumbers.IntNumSymm.proof F K ι V (n + 1) _ _

variable {O : Type u} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

end VerticalDivisorsCommuting

end

end GroundTheory.Heights₂.Heights.NumbersDVR
