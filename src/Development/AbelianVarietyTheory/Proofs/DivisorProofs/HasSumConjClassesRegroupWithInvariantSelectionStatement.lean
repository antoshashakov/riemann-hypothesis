module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSumConjClassesRegroupWithInvariantSelection
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section


theorem _root_.GlobalTheory.T.hasSum_conjClasses_regroup_with_invariant_selection : ∀ {G : Type} [Group G] (g : G → ℂ), (Function.support g).Finite → ∀ (R P : G → Prop), (∀ δ, g δ ≠ 0 → R δ) → (∀ a b, IsConj a b → P a → P b) → HasSum (fun i : {𝔬 : Set G // ∃ γ, R γ ∧ 𝔬 = {δ | IsConj γ δ}} => ∑' δ : i.1, g δ) (∑' δ, g δ) ∧ HasSum (fun i : {𝔬 : Set G // ∃ γ, R γ ∧ 𝔬 = {δ | IsConj γ δ}} => {i : {𝔬 : Set G // ∃ γ, R γ ∧ 𝔬 = {δ | IsConj γ δ}} | ∀ δ ∈ i.1, P δ}.indicator (fun i => ∑' δ : i.1, g δ) i) (∑' δ : {δ // P δ}, g δ) := by
  first | exact @GlobalTheory.classSum_regroup | exact GlobalTheory.classSum_regroup | (intros; apply GlobalTheory.classSum_regroup <;> assumption)
