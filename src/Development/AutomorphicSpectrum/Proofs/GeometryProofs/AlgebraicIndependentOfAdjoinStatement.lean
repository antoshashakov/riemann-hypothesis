module

public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
public import Mathlib.RingTheory.AlgebraicIndependent.Defs
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AlgebraicIndependentOfAdjoin
import Supplements.MathlibImports.AnalysisAndTactics
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsCptGen
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoordTieCompEquiv
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsUnitOfSumEqOne

@[expose] public section

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagBun GlobalTheory.CompanionTheory.Ar.FlagBun.Sm GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.Cell

theorem _root_.GlobalTheory.T.algebraic_independent_of_adjoin : ∀ {Ω K : Type} [Field Ω] [Field K] [Algebra Ω K] {ι : Type} [Finite ι] (u v : ι → K), AlgebraicIndependent Ω u → (∀ a, u a ∈ IntermediateField.adjoin Ω (Set.range v)) → AlgebraicIndependent Ω v := by
  first | exact @GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.Cell.algebraicIndependent_of_mem_adjoin_range | exact GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.Cell.algebraicIndependent_of_mem_adjoin_range | (intros; apply GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.Cell.algebraicIndependent_of_mem_adjoin_range <;> assumption)
