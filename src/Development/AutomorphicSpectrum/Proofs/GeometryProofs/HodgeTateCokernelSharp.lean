module

public import Development.AutomorphicSpectrum.Statements.GeometryStatements.HodgeTateCokerSharp
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Farsharp
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.MathlibImports

@[expose] public section

namespace GlobalTheory.CompanionTheory.Ar.HT

theorem hodge_tate_cokernel_sharp : GlobalTheory.CompanionTheory.Ar.HT.HodgeTateCokerSharp :=
  PositivityTheory.HtPt.Farsharp.hodgeTateCokerSharp

end GlobalTheory.CompanionTheory.Ar.HT
