module

public import Formalism.PolynomialDimension.DigitClassSize
import Formalism.PolynomialDimension.MultinomialDepth.BinomialSeriesBound
public import Formalism.PolynomialDimension.MultinomialDepth.HarmonicLevelCountRec
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

namespace Formalism.CountingSumsFrames.Top

theorem levelCount : Formalism.CountingSumsFrames.LevelCount := Formalism.CountingSumsFrames.harmonic_level_count
theorem densityLower : Formalism.CountingSumsFrames.DensityLower := Formalism.CountingSumsFrames.density_lower_bound

end Formalism.CountingSumsFrames.Top
