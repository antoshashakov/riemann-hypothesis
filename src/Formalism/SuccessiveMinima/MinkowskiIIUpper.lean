module

public import Formalism.SuccessiveMinima.StatementMink
public import Formalism.SuccessiveMinima.SuccessiveMinimaProofs.AdaptedBasis
public import Formalism.SuccessiveMinima.SuccessiveMinimaProofs.GjLevel
public import Formalism.SuccessiveMinima.SuccessiveMinimaProofs.GjScale
public import Formalism.SuccessiveMinima.SuccessiveMinimaProofs.MeasureEqCovolumeMulVolumeImage
public import Formalism.SuccessiveMinima.SuccessiveMinimaProofs.MinkCore
public import Formalism.SuccessiveMinima.SuccessiveMinimaProofs.SuccMin
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

namespace Formalism.FN

theorem minkowskiIIUpper : MinkowskiIIUpper :=
  minkowskiIIUpper_of (minkCore_of partialBoxVolumeMonotoneStep partialBoxVolumeScaling) existsSuccessiveMinimaVectors
    existsAdaptedBasis

end Formalism.FN
