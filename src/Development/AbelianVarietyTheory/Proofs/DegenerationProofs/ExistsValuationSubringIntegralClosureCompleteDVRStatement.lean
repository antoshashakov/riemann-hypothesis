module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsValuationSubringIntegralClosureCompleteDVR
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.MathlibImports

@[expose] public section


theorem _root_.GlobalTheory.T.exists_valuationSubring_integral_closure_completeDVR : ∀ (O : Type) [CommRing O] [IsDomain O] [CharZero O] (ϖ : O), GlobalTheory.LN.ArcBase O ϖ → ∀ (F : Type) [Field F] [Algebra (FractionRing O) F] [Algebra O F] [IsScalarTower O (FractionRing O) F] [Algebra.IsAlgebraic (FractionRing O) F], ∃ S : ValuationSubring F, ∀ x, x ∈ S ↔ IsIntegral O x := by
  first | exact @GlobalTheory.LN.exists_valuationSubring_isIntegral | exact GlobalTheory.LN.exists_valuationSubring_isIntegral | (intros; apply GlobalTheory.LN.exists_valuationSubring_isIntegral <;> assumption)
