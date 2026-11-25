module

public import Mathlib.Analysis.Complex.Order
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.NegDefBlockOfPosDef
import Supplements.MathlibImports.AnalysisAndTactics
import Development.AutomorphicSpectrum.Definitions.AdelicLattices.FactPrimes

@[expose] public section

open NumberField Matrix GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

theorem _root_.GlobalTheory.T.negDef_block_of_posDef : ∀ (p q : ℕ) (A : Matrix (Fin p) (Fin p) ℂ) (B : Matrix (Fin q) (Fin q) ℂ) (C : Matrix (Fin q) (Fin p ⊕ Fin q) ℂ), A.PosDef → B.IsHermitian → (-(C * Matrix.fromBlocks A 0 0 B * Cᴴ)).PosDef → (-B).PosDef := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fl.Sylvester.neg_posDef_of_compl_posDef | exact GlobalTheory.CompanionTheory.Ar.Fl.Sylvester.neg_posDef_of_compl_posDef | (intros; apply GlobalTheory.CompanionTheory.Ar.Fl.Sylvester.neg_posDef_of_compl_posDef <;> assumption)
