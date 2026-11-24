module

public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.GroupTheory.Index
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.ExistsSylowOverSubgroup
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section


theorem _root_.GlobalTheory.T.exists_subgroup_ge_normalizing_not_dvd_relIndex : ∀ (G : Type) [Group G] [Finite G] (C : Subgroup G) (p : ℕ), p.Prime → ∃ H : Subgroup G, C ≤ H ∧ (∀ h ∈ H, ∀ c ∈ C, h * c * h⁻¹ ∈ C) ∧ (∀ h ∈ H, ∃ k : ℕ, h ^ p ^ k ∈ C) ∧ ∀ N : Subgroup G, (∀ g : G, g ∈ N ↔ ∀ c ∈ C, g * c * g⁻¹ ∈ C) → ¬ p ∣ H.relIndex N := by
  first | exact @GlobalTheory.exists_sylow_over_subgroup | exact GlobalTheory.exists_sylow_over_subgroup | (intros; apply GlobalTheory.exists_sylow_over_subgroup <;> assumption)
