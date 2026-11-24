module

public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormInertiaPartialTraceGeometricLe
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MathlibImports
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.norm_inertia_partialTrace_geometric_le : ∀ (l : ℕ) [Fact l.Prime] (γ : GQ l), γ ∈ (MaximalUnramifiedExtension l).fixingSubgroup → ∀ (H : ℕ → Subgroup (GQ l)) (k : ℕ), (∀ n, (H n).Normal) → (∀ n, (H n).index ≠ 0) → (∀ n, (H n).index ≤ l ^ (k + n)) → (∀ n, γ ^ l ^ n ∈ H n) → (∀ n, ∀ h ∈ H n, ∃ i : ℕ, ((γ ^ l ^ n) ^ i)⁻¹ * h ∈ H (n + 1)) → ∃ ρ : ℝ, 0 ≤ ρ ∧ ρ < 1 ∧ ∀ (n : ℕ) (x : Om l), (∀ g ∈ H n, g x = x) → ‖∑ i ∈ Finset.range (l ^ n), (γ ^ i) x‖ ≤ ρ ^ n * ‖x‖ := by
  first | exact @GlobalTheory.PartialTraceGain.norm_sum_pow_le | exact GlobalTheory.PartialTraceGain.norm_sum_pow_le | (intros; apply GlobalTheory.PartialTraceGain.norm_sum_pow_le <;> assumption)
