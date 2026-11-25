module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.Valuation.Integers
public import ReciprocityTheory.DualLattices.TensorSpan
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HopfOrderContainsAddCharacters
import Supplements.MathlibImports.AnalysisAndTactics
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsTight
import ReciprocityTheory.DualLattices.CotangentSurjective

@[expose] public section

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix

theorem _root_.GlobalTheory.T.hopf_order_contains_add_characters : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (N : Type) [AddCommGroup N] [Fintype N] [DecidableEq N], ∀ AA : HopfOrder (C := C) R N, ∀ ψ : AddChar N C, (fun x => ψ x) ∈ AA.carrier := by
  first | exact @GlobalTheory.CompanionTheory.Ar.GR.addChar_mem_hopfOrder | exact GlobalTheory.CompanionTheory.Ar.GR.addChar_mem_hopfOrder | (intros; apply GlobalTheory.CompanionTheory.Ar.GR.addChar_mem_hopfOrder <;> assumption)
