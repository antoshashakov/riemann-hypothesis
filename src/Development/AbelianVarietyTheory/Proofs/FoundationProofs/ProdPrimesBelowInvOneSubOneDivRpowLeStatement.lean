module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.NumberTheory.PrimeCounting
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ProdPrimesBelowInvOneSubOneDivRpowLe
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

open Filter Topology

theorem _root_.GlobalTheory.T.prod_primesBelow_inv_one_sub_rpow_le : ∀ (s : ℝ), 0 < s → ∀ N : ℕ, ∏ p ∈ N.primesBelow, (1 - 1 / (p : ℝ) ^ (1 + s))⁻¹ ≤ 1 + 1 / s := by
  first | exact @GlobalTheory.prod_primesBelow_inv_one_sub_one_div_rpow_le | exact GlobalTheory.prod_primesBelow_inv_one_sub_one_div_rpow_le | (intros; apply GlobalTheory.prod_primesBelow_inv_one_sub_one_div_rpow_le <;> assumption)
