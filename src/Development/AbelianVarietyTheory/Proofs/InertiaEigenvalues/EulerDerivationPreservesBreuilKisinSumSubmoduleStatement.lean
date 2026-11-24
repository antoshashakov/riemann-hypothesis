module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DiagScaleApply
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EulerDerivationPreservesBreuilKisinSumSubmodule
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MathlibImports

@[expose] public section

open PowerSeries GlobalTheory.BK

theorem _root_.GlobalTheory.T.eulerDerivation_preserves_breuilKisin_sum_submodule : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (κ : Type) [Fintype κ] [DecidableEq κ] (η H : ℕ) (D₁ : BKDat O K l e a ι η H) (D₂ : BKDat O K l e a κ η H) (F : BKHom D₁ D₂) (A' b : ℕ), GlobalTheory.IndefiniteRowSideFullHecke.ImageStableDegreeBounds.Reduction O K l e a → ∀ x ∈ GlobalTheory.CokerL.Tsub F A' b, D₂.conn x ∈ GlobalTheory.CokerL.Tsub F A' b := by
  first | exact @GlobalTheory.CokerL.Tsub_conn | exact GlobalTheory.CokerL.Tsub_conn | (intros; apply GlobalTheory.CokerL.Tsub_conn <;> assumption)
