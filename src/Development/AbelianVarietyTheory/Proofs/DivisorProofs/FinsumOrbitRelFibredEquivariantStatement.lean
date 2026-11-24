module

public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Algebra.Group.Subgroup.Actions
public import Mathlib.Basic.Complex.Basic
public import Mathlib.GroupTheory.GroupAction.Defs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumOrbitRelFibredEquivariant
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section


theorem _root_.GlobalTheory.T.finsum_orbitRel_fibred_equivariant : ∀ {H X B E : Type} [Group H] [MulAction H X] [MulAction H B] [MulAction H E] (π : X → B), (∀ (h : H) (x : X), π (h • x) = h • π x) → ∀ (S : B → Subgroup H), (∀ b : B, MulAction.stabilizer H b ≤ S b) → ∀ (j : B → E → X), (∀ b : B, Function.Injective (j b)) → (∀ (b : B) (e : E), π (j b e) = b) → (∀ (b : B) (x : X), π x = b → ∃ e : E, j b e = x) → (∀ (b : B), ∀ h ∈ S b, ∀ e : E, j b (h • e) = h • j b e) → ∀ (s : MulAction.orbitRel.Quotient H B → B), (∀ q, Quotient.mk (MulAction.orbitRel H B) (s q) = q) → ∀ (g : MulAction.orbitRel.Quotient H X → ℂ), (Function.support g).Finite → ∑ᶠ o, g o = ∑ᶠ q, ∑ᶠ o' : MulAction.orbitRel.Quotient (S (s q)) E, g (Quotient.mk (MulAction.orbitRel H X) (j (s q) (Quotient.out o'))) := by
  first | exact @GlobalTheory.finsum_orbitRel_fibred | exact GlobalTheory.finsum_orbitRel_fibred | (intros; apply GlobalTheory.finsum_orbitRel_fibred <;> assumption)
