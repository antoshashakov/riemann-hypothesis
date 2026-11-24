module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.RingTheory.AdjoinRoot
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjoinRootMapComplexLinearIndependent
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

open Filter Topology

theorem _root_.GlobalTheory.T.adjoinRoot_complex_map_linearIndependent : ∀ (D : ℕ) (P : Polynomial (MvPolynomial (Fin D) ℚ)), P.Monic → ∃ τ : AdjoinRoot P →+* AdjoinRoot (P.map (MvPolynomial.map (algebraMap ℚ ℂ))), (∀ i, τ (AdjoinRoot.of P (MvPolynomial.X i)) = AdjoinRoot.of _ (MvPolynomial.X i)) ∧ (∀ (q : ℚ) u, τ (q • u) = (q : ℂ) • τ u) ∧ ∀ (J : Type) (e : J → AdjoinRoot P), LinearIndependent ℚ e → LinearIndependent ℂ (fun j => τ (e j)) := by
  first | exact @GlobalTheory.adjoinRoot_map_complex_linearIndependent | exact GlobalTheory.adjoinRoot_map_complex_linearIndependent | (intros; apply GlobalTheory.adjoinRoot_map_complex_linearIndependent <;> assumption)
