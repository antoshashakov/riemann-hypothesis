module

public import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
public import Mathlib.Basic.Complex.Basic
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.CharacterCosetSumEqZeroOfSubgroupSum
import Supplements.MathlibImports.AnalysisAndTactics
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.InvariantSubspaceMobiusInverseRecEqOfFinrankLt

@[expose] public section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI

theorem _root_.GlobalTheory.T.character_coset_sum_eq_zero_of_subgroup_sum : ∀ (G : Type) [Group G] [Finite G] (χ : G → ℂ), IsChar ℂ ℂ χ → ∀ H : Subgroup G, ∑ᶠ u : H, χ u = 0 → ∀ g : G, ∑ᶠ u : H, χ (g * u) = 0 := by
  first | exact @GlobalTheory.BI.char_coset_sum_eq_zero | exact GlobalTheory.BI.char_coset_sum_eq_zero | (intros; apply GlobalTheory.BI.char_coset_sum_eq_zero <;> assumption)
