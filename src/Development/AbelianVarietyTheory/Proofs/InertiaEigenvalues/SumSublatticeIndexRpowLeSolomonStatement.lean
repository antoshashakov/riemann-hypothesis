module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SumSublatticeIndexRpowLeSolomon
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

open MeasureTheory Filter Topology
open scoped InnerProductSpace BigOperators

theorem _root_.GlobalTheory.T.sum_sublattice_index_rpow_le_solomon : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)] (r : ℕ) (σ : ℝ), (r : ℝ) - 1 < σ → ∀ C : Finset (Submodule O (Fin r → O)), (∀ M ∈ C, M.toAddSubgroup.index ≠ 0) → ∑ M ∈ C, (M.toAddSubgroup.index : ℝ) ^ (-σ) ≤ ∏ i ∈ Finset.range r, (1 - (Nat.card (IsLocalRing.ResidueField O) : ℝ) ^ ((i : ℝ) - σ))⁻¹ := by
  first | exact @GlobalTheory.SubZeta.sum_index_rpow_le | exact GlobalTheory.SubZeta.sum_index_rpow_le | (intros; apply GlobalTheory.SubZeta.sum_index_rpow_le <;> assumption)
