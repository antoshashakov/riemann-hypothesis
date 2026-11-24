module

public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Algebra.Group.Subgroup.Actions
public import Mathlib.Basic.Complex.Basic
public import Mathlib.GroupTheory.GroupAction.Defs
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.SetTheory.Cardinal.Finite
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RootModelPointHeightDegree
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section


theorem _root_.GlobalTheory.T.centralizer_orbit_sum_conjugate : ∀ {Γ Y : Type} [Group Γ] [MulAction Γ Y] (F : Y → Γ → ℂ), (∀ (η : Γ) (y : Y) (γ : Γ), F (η • y) (η * γ * η⁻¹) = F y γ) → ∀ (γ g : Γ), ∑ᶠ o : MulAction.orbitRel.Quotient (Subgroup.centralizer {γ}) Y, ((Nat.card (MulAction.stabilizer Γ (Quotient.out o) ⊓ Subgroup.centralizer {γ} : Subgroup Γ) : ℕ) : ℂ)⁻¹ * F (Quotient.out o) γ = ∑ᶠ o : MulAction.orbitRel.Quotient (Subgroup.centralizer {g * γ * g⁻¹}) Y, ((Nat.card (MulAction.stabilizer Γ (Quotient.out o) ⊓ Subgroup.centralizer {g * γ * g⁻¹} : Subgroup Γ) : ℕ) : ℂ)⁻¹ * F (Quotient.out o) (g * γ * g⁻¹) := by
  first | (exact @GlobalTheory.ClassPart.orbitSum_conj) | (exact GlobalTheory.ClassPart.orbitSum_conj) | (intros; apply GlobalTheory.ClassPart.orbitSum_conj <;> assumption)
