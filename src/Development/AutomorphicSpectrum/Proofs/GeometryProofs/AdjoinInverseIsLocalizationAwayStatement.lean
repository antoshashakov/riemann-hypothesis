module

public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.Algebra.Subalgebra.Lattice
public import Mathlib.RingTheory.Localization.Away.Basic
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AdjoinInverseIsLocalizationAway
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section


theorem _root_.GlobalTheory.T.adjoin_inverse_is_localization_away : ∀ (Ω : Type) [Field Ω] [CharZero Ω] (A S' : Subalgebra ℚ Ω) (G : Set Ω), A = Algebra.adjoin ℚ G →
    ∀ (g : A), g ≠ 0 → S' = Algebra.adjoin ℚ (insert (g : Ω)⁻¹ G) → ∀ (hle : A ≤ S'),
    @IsLocalization.Away A _ g S' _ (Subalgebra.inclusion hle).toRingHom.toAlgebra := by
  first | exact @GlobalTheory.CompanionTheory.Ggeo.adjoin_inv_isLocalization_away | exact GlobalTheory.CompanionTheory.Ggeo.adjoin_inv_isLocalization_away | (intros; apply GlobalTheory.CompanionTheory.Ggeo.adjoin_inv_isLocalization_away <;> assumption)
