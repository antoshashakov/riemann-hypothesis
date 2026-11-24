module

public import Development.AbelianVarietyTheory.Definitions.Divisors.OrthSubrepresentation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusShapeOfSidePreserving
import Supplements.MathlibImports.AnalysisAndTactics
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm

@[expose] public section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

theorem _root_.GlobalTheory.T.base_change_lift_class_function : ∀ (F F' : Type) [Field F] [Field F'] [Algebra F F'] [Finite F'] (s : F' ≃ₐ[F] F'), (∀ t : F' ≃ₐ[F] F', t ∈ Subgroup.zpowers s) → ∀ (n : ℕ) (f : GL (Fin n) F → ℂ), IsCl f → (∀ δ γ, IsNorm s δ γ → shLift s f δ = f γ) ∧ ∀ δ y : GL (Fin n) F', shLift s f (y⁻¹ * δ * galAct F F' n s y) = shLift s f δ := by
  first | (exact @GlobalTheory.Shin.shLift_isNorm_and_twisted_inv) | (exact GlobalTheory.Shin.shLift_isNorm_and_twisted_inv) | (intros; apply GlobalTheory.Shin.shLift_isNorm_and_twisted_inv <;> assumption)
