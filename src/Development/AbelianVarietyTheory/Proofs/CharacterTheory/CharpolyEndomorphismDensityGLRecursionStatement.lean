module

public import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.InvariantSubspaceMobiusInverseRecEqOfFinrankLt
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.CharpolyEndomorphismDensityGLRecursion
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

open Polynomial GlobalTheory.CuspGL

theorem _root_.GlobalTheory.T.charpolyEndomorphismDensityGL_recursion : ∀ (F : Type) [Field F] [Finite F] (P : F[X]), P.Monic → (Nat.card F : ℂ) ^ P.natDegree * mu P = conv (fun _ => 1) mu P ∧ mu (1 : F[X]) = 1 := by
  first | exact @GlobalTheory.CuspGL.mu_rec | exact GlobalTheory.CuspGL.mu_rec | (intros; apply GlobalTheory.CuspGL.mu_rec <;> assumption)
