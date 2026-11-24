module

public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.RingTheory.Finiteness.Defs
public import Development.AutomorphicSpectrum.Proofs.NonGaloisProofs.LinearRelationExactSequenceDim
import Supplements.MathlibImports.AnalysisAndTactics
import Formalism.ConjugateSelfDual.Statement
import Formalism.SharpRestriction.CuspSpanNormBounds.Point
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh

@[expose] public section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module

theorem _root_.GlobalTheory.T.linear_relation_exact_sequence_dim : ∀ (k : Type) [Field k] (H M N Q : Type) [AddCommGroup H] [Module k H] [AddCommGroup M] [Module k M] [AddCommGroup N] [Module k N] [AddCommGroup Q] [Module k Q] [Module.Finite k M] [Module.Finite k N] (a : H →ₗ[k] M) (b : M →ₗ[k] N) (R : Submodule k (N × Q)), Function.Injective a → LinearMap.range a = LinearMap.ker b → (∀ n, ∃ q, (n, q) ∈ R) → (∀ q, ∃ n, (n, q) ∈ R) → (∀ q, (0, q) ∈ R → q = 0) → (∀ n, (n, 0) ∈ R ↔ n ∈ LinearMap.range b) → Module.Finite k Q ∧ finrank k Q + finrank k M = finrank k H + finrank k N := by
  first | exact @GlobalTheory.CompanionTheory.InertiaEigenvalues.finrank_along_relation | exact GlobalTheory.CompanionTheory.InertiaEigenvalues.finrank_along_relation | (intros; apply GlobalTheory.CompanionTheory.InertiaEigenvalues.finrank_along_relation <;> assumption)
