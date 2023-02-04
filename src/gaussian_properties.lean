import measure_theory.decomposition.lebesgue
import measure_theory.measure.lebesgue
import probability.moments
import measure_theory.integral.integrable_on

open measure_theory

-- Let (Ω, σ, ℙ) be a probability space.
variables {Ω : Type} [measurable_space Ω] (ℙ : measure Ω) [is_probability_measure ℙ]

-- Let X be a real-valued random variable on this probability space.
variables (X : Ω → ℝ) (X_measurable : measurable X)
-- Let m and s be some real valued numbers from the set of real values
variables (m s : ℝ)

-- The distribution of the random variable X (a probability measure on ℝ) under ℙ is:
#check ℙ.map X

-- The expected value or Mean of a random variable X can be shown as:
#check ∫ ω, X ω ∂ℙ

-- Another spelling of the same thing using moments is:
#check probability_theory.moment X 1 ℙ

-- The variance of X can be expressed in Lean as:
#check probability_theory.variance X ℙ

-- Another spelling of the same thing also using moments is:
#check probability_theory.central_moment X 2 ℙ


open_locale nnreal ennreal probability_theory measure_theory real

namespace measure_theory

open real

section definitions

-- Defines the probability density function of a gaussian or normal distribution
noncomputable def gaussian_pdf (m s : ℝ) : ℝ → ℝ≥0∞ := 
λ x, ennreal.of_real $ (sqrt (2 * real.pi * s^2))⁻¹ * exp (-(2 * s^2)⁻¹ * (x - m)^2)

-- Defines a gaussian measure the using the pdf defined above 
def measure.real_gaussian (μ : measure ℝ) (m s : ℝ) : Prop := μ = volume.with_density (gaussian_pdf m s)

-- Defines the variance for some random variable X as gaussian
def gaussian_random_variance (X : Ω → ℝ) : Prop := (ℙ.map X).real_gaussian m s

-- Defines a gaussian real valued random variable X on some probability measure ℙ
def gaussian_randon_variable (X : Ω → ℝ): Prop := measure.real_gaussian (ℙ.map X) m s

end definitions

end measure_theory
