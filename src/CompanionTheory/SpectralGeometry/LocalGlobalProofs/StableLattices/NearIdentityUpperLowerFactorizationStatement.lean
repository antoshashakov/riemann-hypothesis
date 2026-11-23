module

public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Topology.MetricSpace.Ultra.Basic
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.NearIdentityUpperLowerFactorization
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

open Matrix

theorem _root_.GlobalTheory.T.near_identity_upper_lower_factorization : ∀ (L : Type) [NontriviallyNormedField L] [IsUltrametricDist L] (n : ℕ) (r : ℝ), 0 ≤ r → r < 1 → ∀ A : Matrix (Fin n) (Fin n) L, (∀ i j, ‖(A - 1) i j‖ ≤ r) → ∃ U W : Matrix (Fin n) (Fin n) L, (∀ i j, j < i → U i j = 0) ∧ (∀ i j, i < j → W i j = 0) ∧ (∀ i j, ‖(U - 1) i j‖ ≤ r) ∧ (∀ i j, ‖(W - 1) i j‖ ≤ r) ∧ A = U * W := by
  first | exact @GlobalTheory.CompanionTheory.CartGL.IwahoriLU.iwahori_factorisation | exact GlobalTheory.CompanionTheory.CartGL.IwahoriLU.iwahori_factorisation | (intros; apply GlobalTheory.CompanionTheory.CartGL.IwahoriLU.iwahori_factorisation <;> assumption)
