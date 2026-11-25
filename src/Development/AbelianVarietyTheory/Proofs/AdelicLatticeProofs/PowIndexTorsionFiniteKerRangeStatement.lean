module

public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.MemPowSub
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.PowIndexTorsionFiniteKerRange
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

theorem _root_.GlobalTheory.T.powIndex_torsion_finite_ker_range : ∀ (p : ℕ) (A A' : Type) [CommGroup A] [CommGroup A'] (g : A →* A'), pIdx p (⊤ : Subgroup A) ≠ 0 → pTor p (⊤ : Subgroup A) ≠ 0 → pTor p g.range ≠ 0 → pIdx p g.ker ≠ 0 ∧ pTor p g.ker ≠ 0 ∧ pIdx p g.range ≠ 0 := by
  first | exact @GlobalTheory.CNorm.pIdx_pTor_ker_range_ne_zero | exact GlobalTheory.CNorm.pIdx_pTor_ker_range_ne_zero | (intros; apply GlobalTheory.CNorm.pIdx_pTor_ker_range_ne_zero <;> assumption)
