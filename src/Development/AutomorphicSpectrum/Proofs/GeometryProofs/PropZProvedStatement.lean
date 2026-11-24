module

public import Development.AutomorphicSpectrum.Statements.GeometryStatements.PropZ
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PropZProved
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.MathlibImports

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat

theorem _root_.GlobalTheory.T.PropZ_proved : GlobalTheory.CompanionTheory.Ar.Flat.PropZ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.PropZ_holds | exact GlobalTheory.CompanionTheory.Ar.Flat.PropZ_holds | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.PropZ_holds <;> assumption)
