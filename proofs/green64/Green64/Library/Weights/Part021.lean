module

public import Green64.Library.Analysis.Estimates.Part004
public import Green64.Library.Weights.Part012
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Green64.Library.Correlation.Part002
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Analysis.Fourier.LpSpace

@[expose] public section

/-!
# Weights / Part021

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceRationalDichotomy -/

section

namespace Green64Analytic.CorrelationD

/-- The exact finite Dirichlet partition: the same reduced
approximant to kθ either has a large denominator (the source
C6 minor-arc case) or places θ on a small-denominator rational
circle arc of radius ≤2R/H' and denominator q<|k|R. -/
theorem source_dirichlet_same_thresholds_split
    (k : ℤ) (theta Hprime R : ℝ)
    (hk : k ≠ 0) (hR : 0 < R)
    (hHR : 2*R ≤ Hprime) :
    ∃ (a : ℤ) (r : ℕ),
      0 < r ∧ r ≤ ⌊Hprime/R⌋₊ ∧
      Int.gcd a (r:ℤ) = 1 ∧
      |(k:ℝ)*theta - (a:ℝ)/(r:ℝ)| ≤ 1/((r:ℝ)^2) ∧
      (R ≤ (r:ℝ) ∨
        ∃ (h0 z : ℤ) (q : ℕ),
          (r:ℝ) < R ∧ q = k.natAbs*r ∧ 0 < q ∧
          (q:ℝ) < (k.natAbs:ℝ)*R ∧
          0 ≤ h0 ∧ h0 < (q:ℤ) ∧
          |theta-(z:ℝ)-(h0:ℝ)/(q:ℝ)| ≤ 2*R/Hprime) := by
  obtain ⟨a,r,q,h0,z,hr,hrCap,hcop,hC6,
      hq,hqpos,hqCap,hh0,hh0lt,hArc⟩ :=
    source_circle_dirichlet_lift k theta Hprime R hk hR hHR
  refine ⟨a,r,hr,hrCap,hcop,hC6,?_⟩
  rcases le_or_gt R (r:ℝ) with hlarge | hsmall
  · exact Or.inl hlarge
  · right
    have hkNat : (0:ℝ) < (k.natAbs:ℝ) := by
      exact_mod_cast ((Int.natAbs_pos).mpr hk)
    have hqCast : (q:ℝ) = (k.natAbs:ℝ)*(r:ℝ) := by
      rw [hq]
      simp only [Nat.cast_mul]
    have hqSmall : (q:ℝ) < (k.natAbs:ℝ)*R := by
      rw [hqCast]
      exact mul_lt_mul_of_pos_left hsmall hkNat
    exact ⟨h0,z,q,hsmall,hq,hqpos,hqSmall,hh0,hh0lt,hArc⟩
end Green64Analytic.CorrelationD

end

/-! ## SourceRealArcParseval -/

section

open MeasureTheory
open scoped BigOperators

/-- Exactly the source additive Fourier-energy interval, using
Lebesgue measure on a REAL arc around any real center.
The bound is valid for radius≤1/2, with no spurious 2π,
and is obtained from normalized AddCircle Parseval and
a full period [center−1/2,center+1/2]. -/
theorem source_real_arc_fourier_energy_le_coeff_l2
    (S : Finset ℕ) (F : ℕ → ℂ)
    (center radius : ℝ)
    (hr : 0 ≤ radius) (hrhalf : radius ≤ 1/2) :
    (∫ theta in (center-radius)..(center+radius),
      ‖sourceNatFourierPoly S F (theta : AddCircle (1:ℝ))‖^2) ≤
      ∑ n ∈ S, ‖F n‖^2 := by
  let G := sourceNatFourierPoly S F
  let f : ℝ → ℝ := fun theta =>
    ‖G (theta : AddCircle (1:ℝ))‖^2
  let c : ℝ := center - 1/2
  let d : ℝ := center + 1/2
  let a : ℝ := center - radius
  let b : ℝ := center + radius
  have hca : c ≤ a := by dsimp [c,a]; linarith
  have hab : a ≤ b := by dsimp [a,b]; linarith
  have hbd : b ≤ d := by dsimp [b,d]; linarith
  have hcont : Continuous f :=
    ((continuous_norm.comp
      (G.continuous.comp (AddCircle.continuous_mk' (1:ℝ)))).pow 2)
  have hint : IntervalIntegrable f volume c d :=
    hcont.intervalIntegrable c d
  have hpos : 0 ≤ᵐ[volume.restrict (Set.Ioc c d)] f :=
    Filter.Eventually.of_forall (fun x => sq_nonneg _)
  have hmono :
      (∫ theta in a..b, f theta) ≤
        ∫ theta in c..d, f theta :=
    intervalIntegral.integral_mono_interval hca hab hbd hpos hint
  have hperiod :
      (∫ theta in c..d, f theta) =
      ∫ x : AddCircle (1:ℝ), ‖G x‖^2
         ∂AddCircle.haarAddCircle := by
    have hcd : c + (1:ℝ) = d := by dsimp [c,d]; ring
    have hh := AddCircle.intervalIntegral_preimage
      (1:ℝ) c (fun x : AddCircle (1:ℝ) => ‖G x‖^2)
    rw [hcd] at hh
    have hhaar := AddCircle.integral_haarAddCircle
      (T := 1) (f := fun x : AddCircle (1:ℝ) => ‖G x‖^2)
    have hhaar' : (∫ x : AddCircle (1:ℝ), ‖G x‖^2
        ∂AddCircle.haarAddCircle) =
      ∫ x : AddCircle (1:ℝ), ‖G x‖^2 := by
        simpa using hhaar
    calc
      (∫ theta in c..d, f theta) =
        ∫ x : AddCircle (1:ℝ), ‖G x‖^2 := by
          simpa only [f] using hh
      _ = ∫ x : AddCircle (1:ℝ), ‖G x‖^2
           ∂AddCircle.haarAddCircle := hhaar'.symm
  have hwhole := source_nat_fourier_arc_energy
    S F (Set.univ : Set (AddCircle (1:ℝ)))
  have hwhole' :
      (∫ x : AddCircle (1:ℝ), ‖G x‖^2
           ∂AddCircle.haarAddCircle) ≤
      ∑ n ∈ S, ‖F n‖^2 := by
    simpa only [Measure.restrict_univ, G] using hwhole
  exact hmono.trans (hperiod.le.trans hwhole')

end

/-! ## SourceBetaArcParseval -/

section

open MeasureTheory
open scoped BigOperators

/-- Exact normalized LOCAL SOURCE Fourier ENERGY integral centered at
arbitrary h/q: the beta window [-1/H,1/H] has at most the full
coefficient L² mass whenever H≥2, with no missing period scaling. -/
theorem source_beta_fourier_energy_le_coeff_l2
    (S : Finset ℕ) (F : ℕ → ℂ) (center H : ℝ)
    (hH : 2 ≤ H) :
    (∫ beta in (-(1/H))..(1/H),
      ‖sourceNatFourierPoly S F
        ((center + beta) : AddCircle (1:ℝ))‖^2) ≤
      ∑ n ∈ S, ‖F n‖^2 := by
  have hHpos : 0 < H := by linarith
  have hrpos : 0 ≤ (1:ℝ)/H := by positivity
  have hrhalf : (1:ℝ)/H ≤ 1/2 :=
    one_div_le_one_div_of_le (by norm_num : (0:ℝ)<2) hH
  let f : ℝ → ℝ := fun t =>
    ‖sourceNatFourierPoly S F (t : AddCircle (1:ℝ))‖^2
  have hshift :
      (∫ beta in (-(1/H))..(1/H), f (center+beta)) =
        ∫ theta in (center - 1/H)..(center + 1/H), f theta := by
    simpa only [sub_eq_add_neg] using
      (intervalIntegral.integral_comp_add_left f center
        (a := -(1/H)) (b := 1/H))
  rw [show (∫ beta in (-(1/H))..(1/H),
      ‖sourceNatFourierPoly S F
        ((center + beta) : AddCircle (1:ℝ))‖^2) =
      ∫ beta in (-(1/H))..(1/H), f (center+beta) from rfl]
  rw [hshift]
  exact source_real_arc_fourier_energy_le_coeff_l2
    S F center (1/H) hrpos hrhalf

/-- Identical source beta-window theorem as a true Lebesgue
set-integral over |beta| ≤ 1/H, not a shorthand for intervals. -/
theorem source_beta_window_fourier_energy_le_coeff_l2
    (S : Finset ℕ) (F : ℕ → ℂ) (center H : ℝ)
    (hH : 2 ≤ H) :
    (∫ beta in {beta : ℝ | |beta| ≤ 1/H},
      ‖sourceNatFourierPoly S F
        ((center+beta) : AddCircle (1:ℝ))‖^2) ≤
      ∑ n ∈ S, ‖F n‖^2 := by
  have hr : 0 ≤ (1:ℝ)/H := by positivity
  have hset : {beta : ℝ | |beta| ≤ 1/H} =
      Set.Icc (-(1/H)) (1/H) := by
    ext beta
    simp only [Set.mem_setOf_eq, Set.mem_Icc, abs_le]
  rw [hset, MeasureTheory.integral_Icc_eq_integral_Ioc]
  rw [← intervalIntegral.integral_of_le (by linarith : -(1/H) ≤ (1/H))]
  exact source_beta_fourier_energy_le_coeff_l2 S F center H hH

end

/-! ## SourceCircleOriginalArc -/

section

open MeasureTheory
namespace Green64Analytic.CorrelationSquare
set_option maxHeartbeats 2200000

/-- Exact bridge from normalized circle measure to the original REAL beta
window. The radius is less than half a period; arcs may wrap around zero. -/
theorem source_circle_closed_ball_energy_eq_beta434
    (F : C(AddCircle (1:ℝ),ℂ)) (center radius : ℝ)
    (hr : 0 ≤ radius) (hrhalf : radius < 1/2) :
    (∫ θ in Metric.closedBall (center:AddCircle (1:ℝ)) radius,
      ‖F θ‖^2 ∂AddCircle.haarAddCircle) =
    ∫ beta in {beta : ℝ | |beta| ≤ radius},
      ‖F ((center+beta:ℝ):AddCircle (1:ℝ))‖^2 := by
  let period := Set.Ioc (center-1/2) (center+1/2)
  let ball := Metric.closedBall (center:AddCircle (1:ℝ)) radius
  let f : ℝ → ℝ := fun t => ‖F (t:AddCircle (1:ℝ))‖^2
  have hPeriod : period ⊆ Metric.closedBall center (|(1:ℝ)|/2) := by
    simpa only [period,abs_one,Real.closedBall_eq_Icc] using Set.Ioc_subset_Icc_self
  have hSmall : Metric.closedBall center radius ⊆ period := by
    intro t ht
    rw [Real.closedBall_eq_Icc] at ht
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hSmallIcc : Set.Icc (center-radius) (center+radius) ⊆ period := by
    simpa only [Real.closedBall_eq_Icc] using hSmall
  have hPre : ((↑) : ℝ → AddCircle (1:ℝ)) ⁻¹' ball ∩ period =
      Set.Icc (center-radius) (center+radius) := by
    have hh := AddCircle.coe_real_preimage_closedBall_inter_eq (p:=1) (ε:=radius) period hPeriod
    simpa only [ball, abs_one, if_pos hrhalf, Real.closedBall_eq_Icc,
      Set.inter_eq_left.mpr hSmallIcc] using hh
  have hBall : MeasurableSet ball := measurableSet_closedBall
  have hPreMeas : MeasurableSet (((↑) : ℝ → AddCircle (1:ℝ)) ⁻¹' ball) :=
    hBall.preimage (AddCircle.continuous_mk' (1:ℝ)).measurable
  have hComp : (fun t : ℝ => ball.indicator (fun θ => ‖F θ‖^2) (t:AddCircle (1:ℝ))) =
      (((↑) : ℝ → AddCircle (1:ℝ)) ⁻¹' ball).indicator f := by
    classical
    funext t
    by_cases ht : (t : AddCircle (1:ℝ)) ∈ ball <;>
      simp [Set.indicator, f, ht]
  have hEnd : center-1/2+(1:ℝ) = center+1/2 := by ring
  have hPeriodIntegral : (∫ θ in ball, ‖F θ‖^2 ∂AddCircle.haarAddCircle) =
      ∫ t in Set.Icc (center-radius) (center+radius), f t := by
    rw [←integral_indicator hBall]
    have hHaar := AddCircle.integral_haarAddCircle (T:=1)
      (f:=ball.indicator (fun θ => ‖F θ‖^2))
    rw [show (∫ θ, ball.indicator (fun θ => ‖F θ‖^2) θ ∂AddCircle.haarAddCircle) =
      ∫ θ, ball.indicator (fun θ => ‖F θ‖^2) θ by simpa using hHaar]
    rw [←AddCircle.integral_preimage (1:ℝ) (center-1/2),hEnd]
    change (∫ t in period, ball.indicator (fun θ => ‖F θ‖^2) (t:AddCircle (1:ℝ))) = _
    rw [hComp,setIntegral_indicator hPreMeas,Set.inter_comm,hPre]
  have hShift : (∫ t in Set.Icc (center-radius) (center+radius), f t) =
      ∫ beta in Set.Icc (-radius) radius, f (center+beta) := by
    rw [integral_Icc_eq_integral_Ioc,integral_Icc_eq_integral_Ioc]
    rw [←intervalIntegral.integral_of_le (by linarith : center-radius ≤ center+radius),
      ←intervalIntegral.integral_of_le (by linarith : -radius ≤ radius)]
    simpa only [sub_eq_add_neg] using
      (intervalIntegral.integral_comp_add_left f center (a := -radius) (b := radius)).symm
  have hBeta : {beta : ℝ | |beta| ≤ radius} = Set.Icc (-radius) radius := by
    ext beta; simp only [Set.mem_setOf_eq,Set.mem_Icc,abs_le]
  simpa only [ball,f,hBeta] using hPeriodIntegral.trans hShift
end Green64Analytic.CorrelationSquare

end

/-! ## SourceManyBetaArcs -/

section

open MeasureTheory
open scoped BigOperators

/-- Arbitrary finite family of rational-arc centers: no disjointness
is needed, and overlapping arcs are harmless. The coefficient L²
budget is spent once per arc. -/
theorem source_many_beta_arcs_energy_le_coeff_l2
    (S : Finset ℕ) (F : ℕ → ℂ) (centers : Finset ℝ)
    (H : ℝ) (hH : 2 ≤ H) :
    (∑ center ∈ centers,
      ∫ beta in {beta : ℝ | |beta| ≤ 1/H},
        ‖sourceNatFourierPoly S F
          ((center+beta) : AddCircle (1:ℝ))‖^2) ≤
      (centers.card : ℝ) * (∑ n ∈ S, ‖F n‖^2) := by
  classical
  calc
    _ ≤ ∑ _center ∈ centers, (∑ n ∈ S, ‖F n‖^2) := by
      apply Finset.sum_le_sum
      intro center hc
      exact source_beta_window_fourier_energy_le_coeff_l2
        S F center H hH
    _ = (centers.card : ℝ) * (∑ n ∈ S, ‖F n‖^2) := by
      simp

end

/-! ## SourceRationalCenterBudget -/

section

open scoped BigOperators

/-- Rational circle arc centers with denominators q ≤ Q and
residues 0≤h<q, exactly as in source sh:arcs. Nonreduced
centers are harmless; repeated rational centers are deduplicated. -/
noncomputable def sourceRationalCenterSet (Q : ℕ) : Finset ℝ := by
  classical
  exact (Finset.range (Q+1)).biUnion
    (fun q => (Finset.range q).image (fun h : ℕ => (h:ℝ)/(q:ℝ)))

theorem source_rational_center_mem
    (Q q h : ℕ) (hq : 0 < q) (hqQ : q ≤ Q) (hh : h < q) :
    (h:ℝ)/(q:ℝ) ∈ sourceRationalCenterSet Q := by
  classical
  unfold sourceRationalCenterSet
  apply Finset.mem_biUnion.mpr
  refine ⟨q, Finset.mem_range.mpr (by omega), ?_⟩
  exact Finset.mem_image.mpr
    ⟨h, Finset.mem_range.mpr hh, rfl⟩

/-- The number of all small rational centers is bounded by
Q(Q+1), with no assumption that reduced fractions are distinct. -/
theorem source_rational_center_card_le (Q : ℕ) :
    (sourceRationalCenterSet Q).card ≤ Q*(Q+1) := by
  classical
  have hcount : (∑ q ∈ Finset.range (Q+1), q) ≤ Q*(Q+1) := by
    induction Q with
    | zero => norm_num
    | succ Q ih =>
      rw [show Q+1+1=Q+2 by omega, Finset.sum_range_succ]
      nlinarith
  calc
    (sourceRationalCenterSet Q).card ≤
      ∑ q ∈ Finset.range (Q+1),
        ((Finset.range q).image (fun h : ℕ => (h:ℝ)/(q:ℝ))).card := by
          unfold sourceRationalCenterSet
          exact Finset.card_biUnion_le
    _ ≤ ∑ q ∈ Finset.range (Q+1), q := by
          apply Finset.sum_le_sum
          intro q hq
          simpa only [Finset.card_range] using
            (Finset.card_image_le
              (s := Finset.range q)
              (f := fun h : ℕ => (h:ℝ)/(q:ℝ)))
    _ ≤ Q*(Q+1) := hcount

end

/-! ## SourceRationalArcBudget -/

section

open MeasureTheory
open scoped BigOperators

/-- The entire source-relevant finite family of rational beta arcs
has total Fourier energy bounded by the exact quadratic center count
times the coefficient square mass. Overlapping arcs are allowed. -/
theorem source_rational_beta_arc_family_energy
    (S : Finset ℕ) (F : ℕ → ℂ) (Q : ℕ)
    (H : ℝ) (hH : 2 ≤ H) :
    (∑ center ∈ sourceRationalCenterSet Q,
      ∫ beta in {beta : ℝ | |beta| ≤ 1/H},
        ‖sourceNatFourierPoly S F
          ((center+beta) : AddCircle (1:ℝ))‖^2) ≤
      ((Q*(Q+1) : ℕ) : ℝ) * (∑ n ∈ S, ‖F n‖^2) := by
  have hsum : 0 ≤ ∑ n ∈ S, ‖F n‖^2 := by
    apply Finset.sum_nonneg
    intro n hn
    positivity
  have hcard : ((sourceRationalCenterSet Q).card : ℝ) ≤
      ((Q*(Q+1):ℕ):ℝ) := by
    exact_mod_cast (source_rational_center_card_le Q)
  calc
    _ ≤ ((sourceRationalCenterSet Q).card:ℝ) *
        (∑ n ∈ S, ‖F n‖^2) :=
          source_many_beta_arcs_energy_le_coeff_l2
            S F (sourceRationalCenterSet Q) H hH
    _ ≤ ((Q*(Q+1):ℕ):ℝ) * (∑ n ∈ S, ‖F n‖^2) :=
      mul_le_mul_of_nonneg_right hcard hsum

/-- Covers the literal source signed rational numerator h
after its reduction to 0≤h<q. -/
theorem source_signed_rational_center_mem
    (Q q : ℕ) (h : ℤ)
    (hq : 0 < q) (hqQ : q ≤ Q)
    (hh0 : 0 ≤ h) (hhq : h < (q:ℤ)) :
    (h:ℝ)/(q:ℝ) ∈ sourceRationalCenterSet Q := by
  have hhCast : ((h.toNat:ℕ):ℤ) = h :=
    Int.toNat_of_nonneg hh0
  have hhNat : h.toNat < q := by
    exact_mod_cast (show ((h.toNat:ℕ):ℤ) < (q:ℤ) by
      simpa [hhCast] using hhq)
  have hmem := source_rational_center_mem Q q h.toNat hq hqQ hhNat
  have hreal : ((h.toNat:ℕ):ℝ) = (h:ℝ) := by
    exact_mod_cast hhCast
  rw [←hreal]
  exact hmem

end

/-! ## SourceLiftedArcPolylog -/

section

/-- Exact source rational-lift budget:
q≤|k| ceil(L^B) and |k|≤L^C imply q≤L^(B+C+1)
for L≥2. The extra 1 absorbs the ceiling and does NOT
require reduced q or any analytic prime input. -/
theorem source_lifted_arc_denominator_polylog
    (L B C : ℝ) (k : ℤ) (q : ℕ)
    (hL : 2 ≤ L) (hB : 0 ≤ B)
    (hk : (k.natAbs : ℝ) ≤ L^C)
    (hq : q ≤ k.natAbs * ⌈L^B⌉₊) :
    (q:ℝ) ≤ L^(B+C+1) := by
  have hLp : 0 < L := by linarith
  have hOne : 1 ≤ L^B := by
    have hh := Real.rpow_le_rpow_of_exponent_le
      (by linarith : (1:ℝ) ≤ L) hB
    simpa only [Real.rpow_zero] using hh
  have hCeil : ((⌈L^B⌉₊:ℕ):ℝ) ≤ 2*L^B := by
    have hlt := Nat.ceil_lt_add_one
      (by positivity : 0 ≤ L^B)
    linarith
  have hqCast : (q:ℝ) ≤ (k.natAbs:ℝ)*((⌈L^B⌉₊:ℕ):ℝ) := by
    exact_mod_cast hq
  have hterm :
      (k.natAbs:ℝ)*((⌈L^B⌉₊:ℕ):ℝ) ≤
        L^C*(2*L^B) := by
    calc
      _ ≤ (k.natAbs:ℝ)*(2*L^B) :=
        mul_le_mul_of_nonneg_left hCeil (by positivity)
      _ ≤ L^C*(2*L^B) :=
        mul_le_mul_of_nonneg_right hk (by positivity)
  have hpow : L^(B+C+1) = L^B*L^C*L := by
    rw [show B+C+1 = (B+C)+1 by ring,
      Real.rpow_add hLp, Real.rpow_add hLp]
    simp only [Real.rpow_one]
  calc
    (q:ℝ) ≤ L^C*(2*L^B) := hqCast.trans hterm
    _ = (L^B*L^C)*2 := by ring
    _ ≤ (L^B*L^C)*L :=
      mul_le_mul_of_nonneg_left hL (by positivity)
    _ = L^(B+C+1) := by rw [hpow]

end

/-! ## SourceActualLiftedCenters -/

section

/-- Every original Dirichlet-lifted circle center h/q with source
|k|≤L^K, q≤|k| ceil(L^B), 0≤h<q lies in the *explicit*
polylogarithmic center family. We do not require the lifted h/q
to be in lowest terms (source 03-shifted correctly does not). -/
theorem source_actual_lifted_center_mem
    (L B K : ℝ) (k h : ℤ) (q : ℕ)
    (hL : 2 ≤ L) (hB : 0 ≤ B)
    (hk : (k.natAbs:ℝ) ≤ L^K)
    (hq : q ≤ k.natAbs*⌈L^B⌉₊)
    (hqpos : 0 < q)
    (hhnonneg : 0 ≤ h) (hhlt : h < (q:ℤ)) :
    (h:ℝ)/(q:ℝ) ∈
      sourceRationalCenterSet ⌈L^(B+K+1)⌉₊ := by
  have hpoly := source_lifted_arc_denominator_polylog
    L B K k q hL hB hk hq
  have hqcap : q ≤ ⌈L^(B+K+1)⌉₊ := by
    have hceil : (q:ℝ) ≤ (⌈L^(B+K+1)⌉₊:ℝ) :=
      hpoly.trans (Nat.le_ceil (L^(B+K+1)))
    exact_mod_cast hceil
  exact source_signed_rational_center_mem
    ⌈L^(B+K+1)⌉₊ q h hqpos hqcap hhnonneg hhlt

end

/-! ## SourceCeilPolylogBudget -/

section

/-- The ceiling needed to capture *all* rational source centers
costs at most one extra fixed logarithmic power. -/
theorem source_ceil_polylog_cap
    (L E : ℝ) (hL : 2 ≤ L) (hE : 0 ≤ E) :
    (⌈L^E⌉₊:ℝ) ≤ L^(E+1) := by
  have hLp : 0 < L := by linarith
  have hOne : (1:ℝ) ≤ L^E := by
    have hh := Real.rpow_le_rpow_of_exponent_le
      (by linarith : (1:ℝ) ≤ L) hE
    simpa only [Real.rpow_zero] using hh
  have hCeil : (⌈L^E⌉₊:ℝ) < L^E+1 :=
    Nat.ceil_lt_add_one (by positivity : (0:ℝ) ≤ L^E)
  have hPow : L^(E+1) = L^E*L := by
    rw [Real.rpow_add hLp]
    simp
  calc
    (⌈L^E⌉₊:ℝ) ≤ L^E+1 := hCeil.le
    _ ≤ 2*L^E := by linarith
    _ ≤ L*L^E := mul_le_mul_of_nonneg_right hL (by positivity)
    _ = L^(E+1) := by rw [hPow]; ring

end

/-! ## SourceRealTimeWeight -/

section

open MeasureTheory
namespace Green64Analytic.CorrelationSquare
set_option maxHeartbeats 750000

/-- Unlike the j=1 expression, the j>=2 real-time collar weight is
truly integrable, so Bochner integration cannot silently default to zero. -/
theorem source_real_time_weight_integrable434
    (h : ℝ) (hh : 0 < h) (j : ℕ) (hj : 2 ≤ j) :
    Integrable (fun t : ℝ => ((1+h*|t|)^j)⁻¹) := by
  apply Integrable.mono' (integrable_inv_one_add_mul_sq hh.ne')
  · have hm : Measurable (fun t : ℝ => ((1+h*|t|)^j)⁻¹) := by fun_prop
    exact hm.aestronglyMeasurable
  · filter_upwards with t
    have hsq : (h*|t|)^2 = (h*t)^2 := by
      calc
        _ = h^2*|t|^2 := by ring
        _ = h^2*t^2 := by rw [sq_abs]
        _ = (h*t)^2 := by ring
    have hz : 0 ≤ h*|t| := mul_nonneg hh.le (abs_nonneg t)
    have hbase : 1+(h*t)^2 ≤ (1+h*|t|)^2 := by nlinarith
    have hpower : (1+h*|t|)^2 ≤ (1+h*|t|)^j :=
      pow_le_pow_right₀ (by linarith) hj
    have hInv : ((1+h*|t|)^j)⁻¹ ≤ (1+(h*t)^2)⁻¹ :=
      (inv_le_inv₀ (by positivity) (by positivity)).mpr (hbase.trans hpower)
    change |((1+h*|t|)^j)⁻¹| ≤ (1+(h*t)^2)⁻¹
    rwa [abs_of_nonneg (by positivity)]

end Green64Analytic.CorrelationSquare

end

/-! ## SourceRealTimeWeightedEnergy -/

section

open MeasureTheory
namespace Green64Analytic.CorrelationSquare
set_option maxHeartbeats 800000

/-- A bounded continuous Mellin polynomial has a genuine full-real-time
weighted second moment for every j ≥ 2, with no cutoff at large |t|. -/
theorem source_real_time_bounded_energy_integrable434
    (h : ℝ) (hh : 0 < h) (j : ℕ) (hj : 2 ≤ j)
    (P : ℝ → ℂ) (hP : Continuous P)
    (M : ℝ) (hM : 0 ≤ M) (hb : ∀ t, ‖P t‖ ≤ M) :
    Integrable (fun t : ℝ => ((1+h*|t|)^j)⁻¹ * ‖P t‖^2) := by
  have hw := source_real_time_weight_integrable434 h hh j hj
  apply Integrable.mono' (hw.const_mul (M^2))
  · have hm : Measurable (fun t : ℝ =>
      ((1+h*|t|)^j)⁻¹ * ‖P t‖^2) := by
      have hPm : Measurable P := hP.measurable
      fun_prop
    exact hm.aestronglyMeasurable
  · filter_upwards with t
    have hbound : ‖P t‖^2 ≤ M^2 :=
      pow_le_pow_left₀ (norm_nonneg _) (hb t) 2
    have hweight : 0 ≤ ((1+h*|t|)^j)⁻¹ := by positivity
    change |((1+h*|t|)^j)⁻¹ * ‖P t‖^2| ≤ M^2 * ((1+h*|t|)^j)⁻¹
    rw [abs_of_nonneg (mul_nonneg hweight (sq_nonneg _))]
    nlinarith [mul_le_mul_of_nonneg_left hbound hweight]
end Green64Analytic.CorrelationSquare

end

/-! ## SourceCollarGramAudit -/

section

open MeasureTheory
namespace Green64Analytic.CorrelationSquare
set_option maxHeartbeats 750000

/-- The physical u=log(v/Y) Jacobian and Fourier normalization
produce 1/Y, not 1/H or 1/Y², after squaring the collar factor.
The 2*pi constants are accounted for separately in inversion. -/
theorem source_collar_normalization_one_over_Y434
    (H Y : ℝ) (hH : 0 < H) (hY : 0 < Y) :
    (Y/H^2) * (H/Y)^2 = 1/Y := by
  field_simp
end Green64Analytic.CorrelationSquare

end

/-! ## SourceCollarFrequencyRows -/

section

open MeasureTheory
namespace Green64Analytic.CorrelationSquare
set_option maxHeartbeats 800000

/-- The angular t shift in the logarithmic Fourier variable is t/(2π).
The t-row has the Jacobian 2π, independent of h, Y, H, and the source labels. -/
theorem source_schur_cycle_frequency_integrable434 (s : ℝ) :
    Integrable (fun t : ℝ =>
      collarSchurWeight434 (s + t / (2 * Real.pi))) := by
  have ha : Integrable (fun x : ℝ => collarSchurWeight434 (s + x)) := by
    convert (collar_schur_weight_shift434 s).1 using 1 with x
    simp only [add_comm]
  exact ha.comp_div (by positivity : (2 * Real.pi) ≠ 0)

theorem source_schur_cycle_frequency_row434 (s : ℝ) :
    (∫ t : ℝ, collarSchurWeight434 (s + t / (2 * Real.pi))) =
      (2 * Real.pi) * (∫ z : ℝ, collarSchurWeight434 z) := by
  calc
    _ = (2 * Real.pi) * (∫ y : ℝ, collarSchurWeight434 (s + y)) := by
      simpa only [smul_eq_mul, abs_of_pos (by positivity : 0 < 2 * Real.pi)] using
        (Measure.integral_comp_div
          (fun y : ℝ => collarSchurWeight434 (s + y)) (2 * Real.pi))
    _ = (2 * Real.pi) * (∫ y : ℝ, collarSchurWeight434 y) := by
      congr 1
      simpa only [add_comm] using
        (integral_add_right_eq_self collarSchurWeight434 s)

/-- The other Schur row has no time Jacobian: integrating in logarithmic
Fourier frequency translates the twice-IBP kernel without a scale loss. -/
theorem source_schur_cycle_spatial_row434 (t : ℝ) :
    Integrable (fun s : ℝ =>
      collarSchurWeight434 (s + t / (2 * Real.pi))) ∧
    (∫ s : ℝ, collarSchurWeight434 (s + t / (2 * Real.pi))) =
      (∫ s : ℝ, collarSchurWeight434 s) := by
  exact collar_schur_weight_shift434 (t / (2 * Real.pi))

/-- Weight ≤ 1 uniformly for arbitrary h≥0 and every j; this is NOT
a source energy-saving hypothesis. -/
theorem source_collar_real_weight_le_one434 (h t : ℝ) (hh : 0 ≤ h)
    (j : ℕ) :
    0 ≤ ((1 + h * |t|)^j)⁻¹ ∧
      ((1 + h * |t|)^j)⁻¹ ≤ 1 := by
  have hbase : 1 ≤ 1 + h * |t| := by
    have ha := mul_nonneg hh (abs_nonneg t)
    linarith
  have hpow : 1 ≤ (1 + h * |t|)^j :=
    one_le_pow₀ hbase
  exact ⟨by positivity, (inv_le_one₀ (by positivity)).mpr hpow⟩
/-- The exact time-frequency Schur row with true collar weight, uniformly
in h,j: no additional h exponent and no assumption on P. -/
theorem source_weighted_cycle_row_bound434 (h : ℝ) (hh : 0 ≤ h)
    (j : ℕ) (s : ℝ) :
    Integrable (fun t : ℝ =>
      ((1 + h * |t|)^j)⁻¹ *
        collarSchurWeight434 (s + t / (2 * Real.pi))) ∧
    (∫ t : ℝ,
      ((1 + h * |t|)^j)⁻¹ *
        collarSchurWeight434 (s + t / (2 * Real.pi))) ≤
      (2 * Real.pi) * (∫ z : ℝ, collarSchurWeight434 z) := by
  let w : ℝ → ℝ := fun t => ((1 + h * |t|)^j)⁻¹
  let phi : ℝ → ℝ := fun t => collarSchurWeight434 (s + t / (2 * Real.pi))
  have hi : Integrable (fun t : ℝ => w t * phi t) := by
    apply Integrable.mono' (source_schur_cycle_frequency_integrable434 s)
    · have hm : Measurable (fun t : ℝ => w t * phi t) := by
        dsimp [w,phi,collarSchurWeight434]
        fun_prop
      exact hm.aestronglyMeasurable
    · filter_upwards with t
      have hw := source_collar_real_weight_le_one434 h t hh j
      have hp := collar_schur_weight_nonneg434 (s + t / (2 * Real.pi))
      change |w t * phi t| ≤ phi t
      rw [abs_of_nonneg (mul_nonneg hw.1 hp)]
      exact mul_le_of_le_one_left hp hw.2
  refine ⟨hi,?_⟩
  calc
    _ ≤ ∫ t : ℝ, phi t :=
      integral_mono hi (source_schur_cycle_frequency_integrable434 s)
        (fun t => mul_le_of_le_one_left
          (collar_schur_weight_nonneg434 _) (source_collar_real_weight_le_one434 h t hh j).2)
    _ = _ := source_schur_cycle_frequency_row434 s
end Green64Analytic.CorrelationSquare

end

/-! ## SourceCollarJointFourier -/

section

open MeasureTheory
open scoped FourierTransform SchwartzMap RealInnerProductSpace
namespace Green64Analytic.CorrelationSquare
set_option maxHeartbeats 1000000

/-- Exact cycle-normalized Fourier integrand for the ACTUAL source symbol.
p.1 is the cycle frequency s; p.2 is the angular Mellin time t. -/
noncomputable def sourceCompactCycleKernel434
    (chi kappa : 𝓢(ℝ,ℂ)) (h : ℝ) (p : ℝ × ℝ) (u : ℝ) : ℂ :=
  Complex.exp (((-2 * Real.pi * (u * p.1) : ℝ) : ℂ) * Complex.I) *
    sourceCompactCollarSymbol434 chi kappa h p.2 u

/-- Joint continuity of the literal source integrand in (s,t,u);
no interval energy bound is assumed. -/
theorem source_compact_cycle_kernel_continuous434
    (chi kappa : 𝓢(ℝ,ℂ)) (h : ℝ) :
    Continuous (fun q : (ℝ × ℝ) × ℝ =>
      sourceCompactCycleKernel434 chi kappa h q.1 q.2) := by
  unfold sourceCompactCycleKernel434 sourceCompactCollarSymbol434 collarZ434
  fun_prop

/-- The true symbol's Fourier transform is continuous jointly in
cycle frequency and Mellin time, by global dominated convergence. -/
theorem source_compact_cycle_integral_continuous434
    (chi kappa : 𝓢(ℝ,ℂ)) (B : ℝ) (hB : 0 < B)
    (hchi : tsupport (chi : ℝ → ℂ) ⊆ Set.Icc (-B) B)
    (h : ℝ) :
    Continuous (fun p : ℝ × ℝ =>
      ∫ u : ℝ, sourceCompactCycleKernel434 chi kappa h p u) := by
  obtain ⟨C,hC,h0⟩ :=
    source_compact_collar_symbol_uniform434 chi kappa B 0
  let S : Set ℝ := Set.Icc (-B) B
  let bound : ℝ → ℝ := S.indicator (fun _ => C)
  have hBoundInt : Integrable bound := by
    dsimp [bound]
    exact (integrableOn_const (s:=S) (by
      dsimp [S]
      rw [Real.volume_Icc]
      exact ENNReal.ofReal_ne_top)).integrable_indicator measurableSet_Icc
  have hMeas (p : ℝ × ℝ) :
      AEStronglyMeasurable (sourceCompactCycleKernel434 chi kappa h p) := by
    have hCont : Continuous (sourceCompactCycleKernel434 chi kappa h p) := by
      have hJoint := source_compact_cycle_kernel_continuous434 chi kappa h
      simpa only [Function.comp_def, id_eq] using
        hJoint.comp (continuous_const.prodMk continuous_id)
    exact hCont.aestronglyMeasurable
  have hDom (p : ℝ × ℝ) :
      ∀ᵐ u : ℝ, ‖sourceCompactCycleKernel434 chi kappa h p u‖ ≤ bound u := by
    apply Filter.Eventually.of_forall
    intro u
    by_cases hu : u ∈ S
    · have huB : |u| ≤ B := abs_le.mpr (Set.mem_Icc.mp hu)
      have hn := h0 h p.2 u huB
      simp only [pow_zero, one_mul] at hn
      have he : ‖sourceCompactCycleKernel434 chi kappa h p u‖ =
          ‖sourceCompactCollarSymbol434 chi kappa h p.2 u‖ := by
        simp only [sourceCompactCycleKernel434, norm_mul,
          Complex.norm_exp_ofReal_mul_I, one_mul]
      simpa only [bound,Set.indicator_of_mem hu,he] using hn
    · simp only [bound, Set.indicator_of_notMem hu]
      have hz : chi u = 0 := by
        by_contra hn
        exact hu (hchi (subset_closure hn))
      simp [sourceCompactCycleKernel434,sourceCompactCollarSymbol434,hz]
  have hParam (u : ℝ) :
      Continuous (fun p : ℝ × ℝ =>
        sourceCompactCycleKernel434 chi kappa h p u) := by
    have hc := source_compact_cycle_kernel_continuous434 chi kappa h
    simpa only [Function.comp_def, id_eq] using
      hc.comp (continuous_id.prodMk continuous_const)
  exact continuous_of_dominated (fun p => hMeas p)
    (fun p => hDom p) hBoundInt (Filter.Eventually.of_forall hParam)
end Green64Analytic.CorrelationSquare

end

/-! ## SourceCollarFourierJoint -/

section

open MeasureTheory
open scoped FourierTransform SchwartzMap
namespace Green64Analytic.CorrelationSquare
set_option maxHeartbeats 850000

/-- The jointly continuous integral from dominated convergence is literally
the Fourier transform of the original source collar, not a surrogate symbol. -/
theorem source_compact_cycle_equals_actual_fourier434
    (chi kappa : 𝓢(ℝ,ℂ)) (h s t : ℝ) :
    (∫ u : ℝ, sourceCompactCycleKernel434 chi kappa h (s,t) u) =
      (𝓕 (sourceCompactCollarSymbol434 chi kappa h t)) s := by
  rw [Real.fourier_eq']
  apply integral_congr_ae
  filter_upwards with u
  simp only [sourceCompactCycleKernel434, Real.inner_apply, smul_eq_mul]

/-- Joint continuity gives measurability for both variables needed in the
original source Fubini and Schur transfers. This is the ACTUAL symbol. -/
theorem source_original_collar_fourier_joint_continuous434
    (chi kappa : 𝓢(ℝ,ℂ)) (B : ℝ) (hB : 0 < B)
    (hchi : tsupport (chi : ℝ → ℂ) ⊆ Set.Icc (-B) B)
    (h : ℝ) :
    Continuous (fun p : ℝ × ℝ =>
      (𝓕 (sourceCompactCollarSymbol434 chi kappa h p.2)) p.1) := by
  have hc := source_compact_cycle_integral_continuous434
    chi kappa B hB hchi h
  convert hc using 1
  ext p
  exact (source_compact_cycle_equals_actual_fourier434 chi kappa h p.1 p.2).symm
theorem source_original_collar_fourier_joint_measurable434
    (chi kappa : 𝓢(ℝ,ℂ)) (B : ℝ) (hB : 0 < B)
    (hchi : tsupport (chi : ℝ → ℂ) ⊆ Set.Icc (-B) B)
    (h : ℝ) :
    Measurable (fun p : ℝ × ℝ =>
      (𝓕 (sourceCompactCollarSymbol434 chi kappa h p.2)) p.1) :=
  (source_original_collar_fourier_joint_continuous434 chi kappa B hB hchi h).measurable

/-- The actual nonnegative Fourier amplitude is jointly continuous, so the
Gram products used in the source Schur/Fubini proof are measurable. -/
theorem source_original_collar_fourier_norm_joint_continuous434
    (chi kappa : 𝓢(ℝ,ℂ)) (B : ℝ) (hB : 0 < B)
    (hchi : tsupport (chi : ℝ → ℂ) ⊆ Set.Icc (-B) B)
    (h : ℝ) :
    Continuous (fun p : ℝ × ℝ =>
      ‖(𝓕 (sourceCompactCollarSymbol434 chi kappa h p.2)) p.1‖) :=
  (source_original_collar_fourier_joint_continuous434 chi kappa B hB hchi h).norm
end Green64Analytic.CorrelationSquare

end

/-! ## SourceCollarCycleFubini -/

section

open MeasureTheory
namespace Green64Analytic.CorrelationSquare
set_option maxHeartbeats 1000000

/-- True angular/cycle frequency Schur majorant on R_s × R_t.
The affine frequency shift is t/(2π); h=H/Y is not discarded. -/
noncomputable def sourceCycleMajorant434
    (h : ℝ) (j : ℕ) (p : ℝ × ℝ) : ℝ :=
  ((1 + h * |p.2|)^j)⁻¹ *
    collarSchurWeight434 (p.1 + p.2 / (2 * Real.pi))

theorem source_cycle_majorant_continuous434 (h : ℝ) (hh : 0 ≤ h) (j : ℕ) :
    Continuous (sourceCycleMajorant434 h j) := by
  unfold sourceCycleMajorant434 collarSchurWeight434
  have hW : Continuous (fun p : ℝ × ℝ => (1 + h * |p.2|)^j) := by fun_prop
  have hwNZ : ∀ p : ℝ × ℝ, (1 + h * |p.2|)^j ≠ 0 := by
    intro p
    have hn : 0 ≤ h * |p.2| := mul_nonneg hh (abs_nonneg _)
    have hp : 0 < 1 + h * |p.2| := by linarith
    exact pow_ne_zero j hp.ne'
  have hP : Continuous (fun p : ℝ × ℝ =>
      (1 + |p.1 + p.2 / (2 * Real.pi)|)^2) := by fun_prop
  have hpNZ : ∀ p : ℝ × ℝ,
      (1 + |p.1 + p.2 / (2 * Real.pi)|)^2 ≠ 0 := by
    intro p
    positivity
  exact (Continuous.inv₀ hW hwNZ).mul (Continuous.inv₀ hP hpNZ)

/-- Integrating the genuine nonnegative product majorant in Fourier
frequency returns the FULL Mellin weight and no 1/h factor. -/
theorem source_cycle_majorant_spatial_mass434
    (h : ℝ) (hh : 0 ≤ h) (j : ℕ) (t : ℝ) :
    (∫ s : ℝ, ‖sourceCycleMajorant434 h j (s,t)‖) =
      ((1 + h * |t|)^j)⁻¹ *
        (∫ s : ℝ, collarSchurWeight434 s) := by
  have hn (s : ℝ) : 0 ≤ sourceCycleMajorant434 h j (s,t) := by
    unfold sourceCycleMajorant434
    have hw := (source_collar_real_weight_le_one434 h t hh j).1
    exact mul_nonneg hw (collar_schur_weight_nonneg434 _)
  simp_rw [Real.norm_eq_abs, abs_of_nonneg (hn _)]
  change (∫ s : ℝ, ((1 + h * |t|)^j)⁻¹ *
    collarSchurWeight434 (s + t / (2 * Real.pi))) = _
  rw [integral_const_mul, (collar_schur_weight_shift434 _).2]

/-- Genuine two-dimensional L¹ gate for Fubini, not a truncated-time
argument or a postulated energy input. -/
theorem source_cycle_majorant_integrable434
    (h : ℝ) (hh : 0 < h) (j : ℕ) (hj : 2 ≤ j) :
    Integrable (sourceCycleMajorant434 h j)
      (volume.prod volume) := by
  have hm : AEStronglyMeasurable (sourceCycleMajorant434 h j)
      (volume.prod volume) :=
    (source_cycle_majorant_continuous434 h hh.le j).aestronglyMeasurable
  apply (integrable_prod_iff' hm).mpr
  constructor
  · apply Filter.Eventually.of_forall
    intro t
    have hs := (collar_schur_weight_shift434 (t / (2 * Real.pi))).1
    have hi := hs.const_mul (((1 + h * |t|)^j)⁻¹)
    simpa only [sourceCycleMajorant434] using hi
  · have hw := source_real_time_weight_integrable434 h hh j hj
    have hi : Integrable (fun t : ℝ =>
        ((1 + h * |t|)^j)⁻¹ *
          (∫ s : ℝ, collarSchurWeight434 s)) :=
      hw.mul_const _
    convert hi using 1
    funext t
    exact source_cycle_majorant_spatial_mass434 h hh.le j t

/-- Absolute source collar majorant permits genuine Fubini on
the entire real-time line, with both tails included. -/
theorem source_cycle_majorant_fubini434
    (h : ℝ) (hh : 0 < h) (j : ℕ) (hj : 2 ≤ j) :
    (∫ s : ℝ, ∫ t : ℝ, sourceCycleMajorant434 h j (s,t)) =
      ∫ t : ℝ, ∫ s : ℝ, sourceCycleMajorant434 h j (s,t) := by
  exact integral_integral_swap (source_cycle_majorant_integrable434 h hh j hj)
end Green64Analytic.CorrelationSquare

end

/-! ## SourceActualCollarLiftContinuity -/

section

open MeasureTheory
open scoped FourierTransform SchwartzMap
namespace Green64Analytic.CorrelationSquare
set_option maxHeartbeats 550000

/-- Exact original Fourier-u lift, with source Mellin angular frequency. -/
noncomputable def sourceActualCollarLift434
    (chi kappa : 𝓢(ℝ,ℂ)) (h : ℝ) (P : ℝ → ℂ)
    (p : ℝ × ℝ) : ℂ :=
  P p.2 * (𝓕 (sourceCompactCollarSymbol434 chi kappa h p.2))
    (p.1 + p.2 / (2 * Real.pi))

theorem source_actual_collar_lift_continuous434
    (chi kappa : 𝓢(ℝ,ℂ)) (B : ℝ) (hB : 0 < B)
    (hchi : tsupport (chi : ℝ → ℂ) ⊆ Set.Icc (-B) B)
    (h : ℝ) (P : ℝ → ℂ) (hP : Continuous P) :
    Continuous (sourceActualCollarLift434 chi kappa h P) := by
  have hFT := source_original_collar_fourier_joint_continuous434
    chi kappa B hB hchi h
  have hshift : Continuous (fun p : ℝ × ℝ =>
      (p.1 + p.2 / (2 * Real.pi), p.2)) :=
    (continuous_fst.add (continuous_snd.div_const _)).prodMk continuous_snd
  change Continuous (fun p : ℝ × ℝ =>
    P p.2 * (𝓕 (sourceCompactCollarSymbol434 chi kappa h p.2))
      (p.1 + p.2 / (2 * Real.pi)))
  have hb := (hP.comp continuous_snd).mul (hFT.comp hshift)
  convert hb using 1 <;> ext p <;> rfl
end Green64Analytic.CorrelationSquare

end

/-! ## SourceActualCollarMajorant -/

section

open MeasureTheory
open scoped FourierTransform SchwartzMap
namespace Green64Analytic.CorrelationSquare
set_option maxHeartbeats 1200000

theorem source_actual_collar_lift_majorant434
    (chi kappa : 𝓢(ℝ,ℂ)) (B : ℝ) (hB : 0 < B)
    (hchi : tsupport (chi : ℝ → ℂ) ⊆ Set.Icc (-B) B)
    (j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (h : ℝ), 0 < h →
      ∀ (P : ℝ → ℂ) (M : ℝ), 0 ≤ M →
      (∀ t : ℝ, ‖P t‖ ≤ M) →
      ∀ p : ℝ × ℝ,
        ‖sourceActualCollarLift434 chi kappa h P p‖ ≤
          (M * C) * sourceCycleMajorant434 h j p := by
  obtain ⟨C,hC,hc⟩ :=
    source_compact_collar_fourier_uniform434 chi kappa B hB hchi j
  refine ⟨C,hC,?_⟩
  intro h hh P M hM hP p
  let freq : ℝ := p.1 + p.2 / (2 * Real.pi)
  have hfreq : 0 < (1 + |freq|)^2 := by positivity
  have htime : 0 < (1 + h * |p.2|)^j := by
    have hp : 0 ≤ h * |p.2| := mul_nonneg hh.le (abs_nonneg _)
    have hbase : 0 < 1 + h * |p.2| := by linarith
    exact pow_pos hbase _
  have hRaw : (1 + |freq|)^2 * (1 + h * |p.2|)^j *
      ‖(𝓕 (sourceCompactCollarSymbol434 chi kappa h p.2)) freq‖ ≤ C := by
    have hr := hc h p.2 freq
    rwa [abs_mul, abs_of_pos hh] at hr
  have hn : ‖(𝓕 (sourceCompactCollarSymbol434 chi kappa h p.2)) freq‖ ≤
      C / ((1 + |freq|)^2 * (1 + h * |p.2|)^j) :=
    (le_div_iff₀ (mul_pos hfreq htime)).mpr (by
      simpa only [mul_assoc, mul_comm, mul_left_comm] using hRaw)
  have hcap : ‖(𝓕 (sourceCompactCollarSymbol434 chi kappa h p.2)) freq‖ ≤
      C * sourceCycleMajorant434 h j p := by
    calc
      _ ≤ C / ((1 + |freq|)^2 * (1 + h * |p.2|)^j) := hn
      _ = C * sourceCycleMajorant434 h j p := by
        simp [sourceCycleMajorant434, collarSchurWeight434, freq,
          div_eq_mul_inv, mul_inv_rev, mul_comm, mul_left_comm, mul_assoc]
  have hm : 0 ≤ sourceCycleMajorant434 h j p := by
    unfold sourceCycleMajorant434
    exact mul_nonneg (source_collar_real_weight_le_one434 h p.2 hh.le j).1
      (collar_schur_weight_nonneg434 _)
  calc
    ‖sourceActualCollarLift434 chi kappa h P p‖ =
        ‖P p.2‖ * ‖(𝓕 (sourceCompactCollarSymbol434 chi kappa h p.2)) freq‖ := by
          simp only [sourceActualCollarLift434, norm_mul, freq]
    _ ≤ M * (C * sourceCycleMajorant434 h j p) :=
      mul_le_mul (hP p.2) hcap (norm_nonneg _) hM
    _ = _ := by ring
end Green64Analytic.CorrelationSquare

end

/-! ## SourceActualCollarFullFubini -/

section

open MeasureTheory
open scoped FourierTransform SchwartzMap
namespace Green64Analytic.CorrelationSquare
set_option maxHeartbeats 1200000

theorem source_actual_collar_lift_integrable434
    (chi kappa : 𝓢(ℝ,ℂ)) (B : ℝ) (hB : 0 < B)
    (hchi : tsupport (chi : ℝ → ℂ) ⊆ Set.Icc (-B) B)
    (j : ℕ) (hj : 2 ≤ j) (h : ℝ) (hh : 0 < h)
    (P : ℝ → ℂ) (hP : Continuous P)
    (M : ℝ) (hM : 0 ≤ M) (hBound : ∀ t, ‖P t‖ ≤ M) :
    Integrable (sourceActualCollarLift434 chi kappa h P)
      (volume.prod volume) := by
  obtain ⟨C,hC,hmax⟩ :=
    source_actual_collar_lift_majorant434 chi kappa B hB hchi j
  have hInt := (source_cycle_majorant_integrable434 h hh j hj).const_mul (M*C)
  apply Integrable.mono' hInt
    (source_actual_collar_lift_continuous434 chi kappa B hB hchi h P hP).aestronglyMeasurable
  filter_upwards with p
  exact hmax h hh P M hM hBound p

/-- Exact complex Bochner Fubini for the original source lift,
without truncating positive or negative times. -/
theorem source_actual_collar_lift_fubini434
    (chi kappa : 𝓢(ℝ,ℂ)) (B : ℝ) (hB : 0 < B)
    (hchi : tsupport (chi : ℝ → ℂ) ⊆ Set.Icc (-B) B)
    (j : ℕ) (hj : 2 ≤ j) (h : ℝ) (hh : 0 < h)
    (P : ℝ → ℂ) (hP : Continuous P)
    (M : ℝ) (hM : 0 ≤ M) (hBound : ∀ t, ‖P t‖ ≤ M) :
    (∫ s : ℝ, ∫ t : ℝ,
       sourceActualCollarLift434 chi kappa h P (s,t)) =
      (∫ t : ℝ, ∫ s : ℝ,
        sourceActualCollarLift434 chi kappa h P (s,t)) := by
  exact integral_integral_swap (source_actual_collar_lift_integrable434
    chi kappa B hB hchi j hj h hh P hP M hM hBound)
end Green64Analytic.CorrelationSquare

end

/-! ## SourceSchurCauchy -/

section

open MeasureTheory
namespace Green64Analytic.CorrelationSquare
set_option maxHeartbeats 600000

/-- Cauchy–Schwarz for truly square-integrable nonnegative real functions
on the entire line. A finite L1 cut-off is NOT inserted. -/
theorem source_weighted_real_cauchy434
    (f g : ℝ → ℝ) (hf : Continuous f) (hg : Continuous g)
    (hf0 : ∀ t, 0 ≤ f t) (hg0 : ∀ t, 0 ≤ g t)
    (hf2 : Integrable (fun t : ℝ => (f t)^2))
    (hg2 : Integrable (fun t : ℝ => (g t)^2)) :
    (∫ t : ℝ, f t * g t)^2 ≤
      (∫ t : ℝ, (f t)^2) * (∫ t : ℝ, (g t)^2) := by
  have hc : (2:ℝ).HolderConjugate 2 :=
    ⟨by norm_num, by norm_num, by norm_num⟩
  have hfl : MemLp f 2 volume :=
    (memLp_two_iff_integrable_sq hf.aestronglyMeasurable).mpr hf2
  have hgl : MemLp g 2 volume :=
    (memLp_two_iff_integrable_sq hg.aestronglyMeasurable).mpr hg2
  have hfR : MemLp f (ENNReal.ofReal (2:ℝ)) volume := by
    simpa using hfl
  have hgR : MemLp g (ENNReal.ofReal (2:ℝ)) volume := by
    simpa using hgl
  have hcs := integral_mul_le_Lp_mul_Lq_of_nonneg hc
    (Filter.Eventually.of_forall hf0) (Filter.Eventually.of_forall hg0)
    hfR hgR
  have hA : 0 ≤ (∫ t : ℝ, (f t)^2) :=
    integral_nonneg (fun t => sq_nonneg _)
  have hB : 0 ≤ (∫ t : ℝ, (g t)^2) :=
    integral_nonneg (fun t => sq_nonneg _)
  have hC : 0 ≤ (∫ t : ℝ, f t*g t) :=
    integral_nonneg (fun t => mul_nonneg (hf0 _) (hg0 _))
  have hfPower (t : ℝ) : f t ^ (2:ℝ) = f t ^ (2:ℕ) :=
    Real.rpow_natCast (f t) 2
  have hgPower (t : ℝ) : g t ^ (2:ℝ) = g t ^ (2:ℕ) :=
    Real.rpow_natCast (g t) 2
  simp_rw [hfPower, hgPower] at hcs
  have hsqrt : (∫ t : ℝ, f t*g t) ≤
      Real.sqrt (∫ t : ℝ, (f t)^2) *
      Real.sqrt (∫ t : ℝ, (g t)^2) := by
    simpa only [Real.sqrt_eq_rpow, one_div] using hcs
  have hsq := pow_le_pow_left₀ hC hsqrt 2
  nlinarith [Real.sq_sqrt hA, Real.sq_sqrt hB,
      sq_nonneg (Real.sqrt (∫ t : ℝ, (f t)^2)),
      sq_nonneg (Real.sqrt (∫ t : ℝ, (g t)^2))]
end Green64Analytic.CorrelationSquare

end

/-! ## SourceActualCollarModulation -/

section

open MeasureTheory
open scoped FourierTransform SchwartzMap RealInnerProductSpace
namespace Green64Analytic.CorrelationSquare
set_option maxHeartbeats 1100000

/-- Exact Fourier-u frequency shift induced by the ORIGINAL logarithmic
Mellin factor exp(-iut). Frequencies are in cycles for Fourier-u,
but t is angular: hence t/(2π), including the sign. -/
theorem source_original_collar_modulation_shift434
    (chi kappa : 𝓢(ℝ,ℂ)) (h s t : ℝ) :
    (∫ u : ℝ,
      Complex.exp (((-2 * Real.pi * (u*s) : ℝ) : ℂ) * Complex.I) *
      Complex.exp (((-(u*t) : ℝ) : ℂ) * Complex.I) *
      sourceCompactCollarSymbol434 chi kappa h t u) =
      (𝓕 (sourceCompactCollarSymbol434 chi kappa h t))
        (s + t/(2 * Real.pi)) := by
  rw [Real.fourier_eq']
  apply integral_congr_ae
  filter_upwards with u
  rw [Real.inner_apply, ← Complex.exp_add]
  congr 1
  have hpi : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  push_cast
  congr 1
  field_simp
  ring
end Green64Analytic.CorrelationSquare

end

/-! ## SourceKernelCauchy -/

section

open MeasureTheory
namespace Green64Analytic.CorrelationSquare
set_option maxHeartbeats 850000

/-- Weighted Cauchy–Schwarz in the exact form needed for the real
compact-center Schur kernel and an actual complex Mellin polynomial. -/
theorem source_kernel_weighted_cauchy434
    (k : ℝ → ℝ) (hk : Continuous k)
    (hk0 : ∀ t, 0 ≤ k t) (hki : Integrable k)
    (P : ℝ → ℂ) (hP : Continuous P)
    (M : ℝ) (hM : 0 ≤ M) (hBound : ∀ t, ‖P t‖ ≤ M) :
    (∫ t : ℝ, k t * ‖P t‖)^2 ≤
      (∫ t : ℝ, k t) * (∫ t : ℝ, k t * ‖P t‖^2) := by
  let f : ℝ → ℝ := fun t => Real.sqrt (k t)
  let g : ℝ → ℝ := fun t => Real.sqrt (k t) * ‖P t‖
  have hf : Continuous f := Real.continuous_sqrt.comp hk
  have hg : Continuous g := hf.mul hP.norm
  have hf0 (t : ℝ) : 0 ≤ f t := Real.sqrt_nonneg _
  have hg0 (t : ℝ) : 0 ≤ g t :=
    mul_nonneg (hf0 _) (norm_nonneg _)
  have hfsq (t : ℝ) : f t ^ 2 = k t := Real.sq_sqrt (hk0 t)
  have hgsq (t : ℝ) : g t ^ 2 = k t * ‖P t‖^2 := by
    dsimp [g]
    rw [mul_pow, Real.sq_sqrt (hk0 t)]
  have hfi : Integrable (fun t : ℝ => f t ^ 2) := by
    simpa only [hfsq] using hki
  have hkiP : Integrable (fun t : ℝ => k t * ‖P t‖^2) := by
    apply Integrable.mono' (hki.const_mul (M^2))
    · have hm : Measurable (fun t : ℝ => k t * ‖P t‖^2) := by
        fun_prop
      exact hm.aestronglyMeasurable
    · filter_upwards with t
      have hsq : ‖P t‖^2 ≤ M^2 :=
        pow_le_pow_left₀ (norm_nonneg _) (hBound t) 2
      change |k t * ‖P t‖^2| ≤ M^2 * k t
      rw [abs_of_nonneg (mul_nonneg (hk0 t) (sq_nonneg _))]
      nlinarith [mul_le_mul_of_nonneg_left hsq (hk0 t)]
  have hgi : Integrable (fun t : ℝ => g t ^ 2) := by
    simpa only [hgsq] using hkiP
  have hfg (t : ℝ) : f t * g t = k t * ‖P t‖ := by
    dsimp [f,g]
    rw [← mul_assoc, Real.mul_self_sqrt (hk0 t)]
  have hcs := source_weighted_real_cauchy434 f g hf hg hf0 hg0 hfi hgi
  simpa only [hfg, hfsq, hgsq] using hcs
end Green64Analytic.CorrelationSquare

end

/-! ## SourceActualSchurCauchy -/

section

open MeasureTheory
namespace Green64Analytic.CorrelationSquare
set_option maxHeartbeats 600000

/-- The source cycle kernel is continuous in angular t at each real cycle s. -/
theorem source_cycle_majorant_time_continuous434
    (h : ℝ) (hh : 0 ≤ h) (j : ℕ) (s : ℝ) :
    Continuous (fun t : ℝ => sourceCycleMajorant434 h j (s,t)) := by
  exact (source_cycle_majorant_continuous434 h hh j).comp
    (continuous_const.prodMk continuous_id)

/-- The source cycle kernel has a positive pointwise density. -/
theorem source_cycle_majorant_nonneg434
    (h : ℝ) (hh : 0 ≤ h) (j : ℕ) (s t : ℝ) :
    0 ≤ sourceCycleMajorant434 h j (s,t) := by
  unfold sourceCycleMajorant434
  exact mul_nonneg (source_collar_real_weight_le_one434 h t hh j).1
    (collar_schur_weight_nonneg434 _)

/-- Weighted time Cauchy–Schwarz for the actual source cycle kernel,
including the exact source angular-to-cycle shift t/(2π). -/
theorem source_actual_cycle_kernel_cauchy434
    (h : ℝ) (hh : 0 < h) (j : ℕ) (s : ℝ)
    (P : ℝ → ℂ) (hP : Continuous P)
    (M : ℝ) (hM : 0 ≤ M) (hBound : ∀ t, ‖P t‖ ≤ M) :
    (∫ t : ℝ, sourceCycleMajorant434 h j (s,t) * ‖P t‖)^2 ≤
      (∫ t : ℝ, sourceCycleMajorant434 h j (s,t)) *
      (∫ t : ℝ, sourceCycleMajorant434 h j (s,t) * ‖P t‖^2) := by
  let k : ℝ → ℝ := fun t => sourceCycleMajorant434 h j (s,t)
  have hc : Continuous k :=
    source_cycle_majorant_time_continuous434 h hh.le j s
  have hn (t : ℝ) : 0 ≤ k t :=
    source_cycle_majorant_nonneg434 h hh.le j s t
  have hi : Integrable k := by
    simpa only [k,sourceCycleMajorant434] using
      (source_weighted_cycle_row_bound434 h hh.le j s).1
  exact source_kernel_weighted_cauchy434 k hc hn hi
    P hP M hM hBound

/-- Explicit source time Schur row bound; no factors of 1/h. -/
theorem source_actual_cycle_kernel_row434
    (h : ℝ) (hh : 0 < h) (j : ℕ) (s : ℝ) :
    (∫ t : ℝ, sourceCycleMajorant434 h j (s,t)) ≤
    (2*Real.pi) * (∫ z : ℝ, collarSchurWeight434 z) := by
  simpa only [sourceCycleMajorant434] using
    (source_weighted_cycle_row_bound434 h hh.le j s).2
end Green64Analytic.CorrelationSquare

end

/-! ## SourceActualLiftWeightedBound -/

section

open MeasureTheory
open scoped FourierTransform SchwartzMap
namespace Green64Analytic.CorrelationSquare
set_option maxHeartbeats 850000

/-- The source collar Fourier-u amplitude times the exact ACTUAL |P(t)|.
This is strictly stronger than the earlier uniform L∞ bound M*C*kernel
and is essential for the true L² estimate with no artificial source saving. -/
theorem source_actual_lift_weighted_pointwise434
    (chi kappa : 𝓢(ℝ,ℂ)) (B : ℝ) (hB : 0 < B)
    (hchi : tsupport (chi : ℝ → ℂ) ⊆ Set.Icc (-B) B)
    (j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (h : ℝ), 0 < h →
      ∀ (P : ℝ → ℂ) (s t : ℝ),
        ‖sourceActualCollarLift434 chi kappa h P (s,t)‖ ≤
          C * (sourceCycleMajorant434 h j (s,t) * ‖P t‖) := by
  obtain ⟨C,hC,hmax⟩ :=
    source_actual_collar_lift_majorant434 chi kappa B hB hchi j
  refine ⟨C,hC,?_⟩
  intro h hh P s t
  have hconst := hmax h hh (fun _ : ℝ => (1:ℂ)) 1
    (by norm_num) (fun _ => by norm_num) (s,t)
  have hFourier :
      ‖(𝓕 (sourceCompactCollarSymbol434 chi kappa h t))
          (s + t / (2*Real.pi))‖ ≤
        C*sourceCycleMajorant434 h j (s,t) := by
    simpa only [sourceActualCollarLift434, norm_mul, norm_one, one_mul]
      using hconst
  calc
    ‖sourceActualCollarLift434 chi kappa h P (s,t)‖ =
        ‖P t‖ * ‖(𝓕 (sourceCompactCollarSymbol434 chi kappa h t))
            (s + t / (2*Real.pi))‖ := by
      simp only [sourceActualCollarLift434, norm_mul]
    _ ≤ ‖P t‖ * (C*sourceCycleMajorant434 h j (s,t)) :=
      mul_le_mul_of_nonneg_left hFourier (norm_nonneg _)
    _ = C*(sourceCycleMajorant434 h j (s,t)*‖P t‖) := by ring
end Green64Analytic.CorrelationSquare

end

/-! ## SourceActualLiftIntegral -/

section

open MeasureTheory
open scoped FourierTransform SchwartzMap
namespace Green64Analytic.CorrelationSquare
set_option maxHeartbeats 1250000

/-- True complex source Fourier lift, integrated in unbounded angular time,
is controlled by the weighted Schur kernel times |P|, not sup|P|. -/
theorem source_actual_lift_integral_row434
    (chi kappa : 𝓢(ℝ,ℂ)) (B : ℝ) (hB : 0 < B)
    (hchi : tsupport (chi : ℝ → ℂ) ⊆ Set.Icc (-B) B)
    (j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (h : ℝ), 0 < h →
      ∀ (P : ℝ → ℂ) (hP : Continuous P)
        (M : ℝ) (hM : 0 ≤ M) (hBound : ∀ t, ‖P t‖ ≤ M)
        (s : ℝ),
        Integrable (fun t : ℝ =>
          sourceActualCollarLift434 chi kappa h P (s,t)) ∧
        ‖∫ t : ℝ, sourceActualCollarLift434 chi kappa h P (s,t)‖ ≤
          C * (∫ t : ℝ, sourceCycleMajorant434 h j (s,t) * ‖P t‖) := by
  obtain ⟨C,hC,hmajor⟩ :=
    source_actual_lift_weighted_pointwise434 chi kappa B hB hchi j
  refine ⟨C,hC,?_⟩
  intro h hh P hP M hM hBound s
  let k : ℝ → ℝ := fun t => sourceCycleMajorant434 h j (s,t)
  have hki : Integrable k := by
    simpa only [k,sourceCycleMajorant434] using
      (source_weighted_cycle_row_bound434 h hh.le j s).1
  have hkcont : Continuous k :=
    source_cycle_majorant_time_continuous434 h hh.le j s
  have hk0 (t : ℝ) : 0 ≤ k t :=
    source_cycle_majorant_nonneg434 h hh.le j s t
  have hkiP : Integrable (fun t : ℝ => k t * ‖P t‖) := by
    apply Integrable.mono' (hki.const_mul M)
    · exact (hkcont.mul hP.norm).aestronglyMeasurable
    · filter_upwards with t
      change |k t * ‖P t‖| ≤ M * k t
      rw [abs_of_nonneg (mul_nonneg (hk0 t) (norm_nonneg _))]
      exact (mul_le_mul_of_nonneg_left (hBound t) (hk0 t)).trans_eq
        (mul_comm _ _)
  have hcont : Continuous (fun t : ℝ =>
      sourceActualCollarLift434 chi kappa h P (s,t)) := by
    exact (source_actual_collar_lift_continuous434
      chi kappa B hB hchi h P hP).comp
        (continuous_const.prodMk continuous_id)
  have hBoundLift (t : ℝ) :
      ‖sourceActualCollarLift434 chi kappa h P (s,t)‖ ≤
        C * (k t * ‖P t‖) :=
    hmajor h hh P s t
  have hInt : Integrable (fun t : ℝ =>
      sourceActualCollarLift434 chi kappa h P (s,t)) := by
    apply Integrable.mono' (hkiP.const_mul C) hcont.aestronglyMeasurable
    filter_upwards with t
    exact hBoundLift t
  refine ⟨hInt,?_⟩
  calc
    _ ≤ ∫ t : ℝ, ‖sourceActualCollarLift434 chi kappa h P (s,t)‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ t : ℝ, C*(k t*‖P t‖) :=
      integral_mono hInt.norm (hkiP.const_mul C) hBoundLift
    _ = C*(∫ t : ℝ, k t*‖P t‖) := integral_const_mul _ _
end Green64Analytic.CorrelationSquare

end

/-! ## SourceActualLiftPointwiseL2 -/

section

open MeasureTheory
open scoped FourierTransform SchwartzMap
namespace Green64Analytic.CorrelationSquare
set_option maxHeartbeats 1400000

/-- Original source, untruncated real-time Fourier lift: its pointwise
energy has a genuine Schur bound by the full weighted Mellin L² row.
The constant is uniform in source h=H/Y, s, t, and the original labels. -/
theorem source_actual_lift_pointwise_energy434
    (chi kappa : 𝓢(ℝ,ℂ)) (B : ℝ) (hB : 0 < B)
    (hchi : tsupport (chi : ℝ → ℂ) ⊆ Set.Icc (-B) B)
    (j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (h : ℝ), 0 < h →
      ∀ (P : ℝ → ℂ) (hP : Continuous P)
        (M : ℝ) (hM : 0 ≤ M) (hBound : ∀ t, ‖P t‖ ≤ M)
        (s : ℝ),
        ‖∫ t : ℝ, sourceActualCollarLift434 chi kappa h P (s,t)‖^2 ≤
          C^2 * ((2*Real.pi) * (∫ z : ℝ, collarSchurWeight434 z)) *
            (∫ t : ℝ, sourceCycleMajorant434 h j (s,t) * ‖P t‖^2) := by
  obtain ⟨C,hC,hrowLift⟩ :=
    source_actual_lift_integral_row434 chi kappa B hB hchi j
  refine ⟨C,hC,?_⟩
  intro h hh P hP M hM hBound s
  let R : ℝ := ∫ t : ℝ, sourceCycleMajorant434 h j (s,t)
  let W : ℝ := ∫ t : ℝ, sourceCycleMajorant434 h j (s,t) * ‖P t‖^2
  let A : ℝ := ∫ t : ℝ, sourceCycleMajorant434 h j (s,t) * ‖P t‖
  let J : ℝ := (2*Real.pi) * (∫ z : ℝ, collarSchurWeight434 z)
  have hR0 : 0 ≤ R := integral_nonneg
    (fun t => source_cycle_majorant_nonneg434 h hh.le j s t)
  have hW0 : 0 ≤ W := integral_nonneg
    (fun t => mul_nonneg
      (source_cycle_majorant_nonneg434 h hh.le j s t) (sq_nonneg _))
  have hA0 : 0 ≤ A := integral_nonneg
    (fun t => mul_nonneg
      (source_cycle_majorant_nonneg434 h hh.le j s t) (norm_nonneg _))
  have hR : R ≤ J := source_actual_cycle_kernel_row434 h hh j s
  have hCS : A^2 ≤ R*W :=
    source_actual_cycle_kernel_cauchy434 h hh j s P hP M hM hBound
  have hLift : ‖∫ t : ℝ,
      sourceActualCollarLift434 chi kappa h P (s,t)‖ ≤ C*A :=
    (hrowLift h hh P hP M hM hBound s).2
  have hPowsq := pow_le_pow_left₀ (norm_nonneg _) hLift 2
  have hRmul : R*W ≤ J*W := mul_le_mul_of_nonneg_right hR hW0
  calc
    _ ≤ (C*A)^2 := hPowsq
    _ = C^2*A^2 := by ring
    _ ≤ C^2*(R*W) := mul_le_mul_of_nonneg_left hCS (sq_nonneg C)
    _ ≤ C^2*(J*W) := mul_le_mul_of_nonneg_left hRmul (sq_nonneg C)
    _ = _ := by ring
end Green64Analytic.CorrelationSquare

end

/-! ## SourceActualSchurEnergyFubini -/

section

open MeasureTheory
namespace Green64Analytic.CorrelationSquare
set_option maxHeartbeats 950000

/-- Source cycle Schur kernel times the ACTUAL squared complex Mellin norm;
no replacement by a constant energy-saving hypothesis. -/
noncomputable def sourceCycleEnergyKernel434
    (h : ℝ) (j : ℕ) (P : ℝ → ℂ) (p : ℝ × ℝ) : ℝ :=
  sourceCycleMajorant434 h j p * ‖P p.2‖^2

theorem source_cycle_energy_kernel_continuous434
    (h : ℝ) (hh : 0 ≤ h) (j : ℕ) (P : ℝ → ℂ) (hP : Continuous P) :
    Continuous (sourceCycleEnergyKernel434 h j P) := by
  unfold sourceCycleEnergyKernel434
  exact (source_cycle_majorant_continuous434 h hh j).mul
    ((hP.comp continuous_snd).norm.pow 2)

theorem source_cycle_energy_kernel_nonneg434
    (h : ℝ) (hh : 0 ≤ h) (j : ℕ) (P : ℝ → ℂ) (p : ℝ × ℝ) :
    0 ≤ sourceCycleEnergyKernel434 h j P p :=
  mul_nonneg (source_cycle_majorant_nonneg434 h hh j p.1 p.2)
    (sq_nonneg _)

/-- Genuine R² absolute-integrability of the exact squared-P Schur kernel.
h>0 and j>=2 are sufficient; no truncation to |t|<=T. -/
theorem source_cycle_energy_kernel_integrable434
    (h : ℝ) (hh : 0 < h) (j : ℕ) (hj : 2 ≤ j)
    (P : ℝ → ℂ) (hP : Continuous P)
    (M : ℝ) (hM : 0 ≤ M) (hBound : ∀ t, ‖P t‖ ≤ M) :
    Integrable (sourceCycleEnergyKernel434 h j P) (volume.prod volume) := by
  apply Integrable.mono'
    ((source_cycle_majorant_integrable434 h hh j hj).const_mul (M^2))
    (source_cycle_energy_kernel_continuous434 h hh.le j P hP).aestronglyMeasurable
  filter_upwards with p
  have hp := source_cycle_majorant_nonneg434 h hh.le j p.1 p.2
  have hsq : ‖P p.2‖^2 ≤ M^2 :=
    pow_le_pow_left₀ (norm_nonneg _) (hBound p.2) 2
  change |sourceCycleMajorant434 h j p * ‖P p.2‖^2| ≤
    M^2 * sourceCycleMajorant434 h j p
  rw [abs_of_nonneg (mul_nonneg hp (sq_nonneg _))]
  nlinarith [mul_le_mul_of_nonneg_left hsq hp]

/-- Exact s-row after insertion of the original P(t)²:
the t/(2π) shift has NO Jacobian when s is the integration variable. -/
theorem source_cycle_energy_spatial_row434
    (h : ℝ) (j : ℕ) (t : ℝ) (P : ℝ → ℂ) :
    (∫ s : ℝ, sourceCycleEnergyKernel434 h j P (s,t)) =
      ((1+h*|t|)^j)⁻¹ *
        (∫ s : ℝ, collarSchurWeight434 s) * ‖P t‖^2 := by
  simp only [sourceCycleEnergyKernel434, sourceCycleMajorant434]
  rw [integral_mul_const, integral_const_mul]
  rw [(collar_schur_weight_shift434 (t/(2*Real.pi))).2]
/-- Real-time and cycle-frequency integrals commute with the TRUE
squared P-weight, and yield exactly one t-weight plus the spatial mass. -/
theorem source_cycle_energy_fubini434
    (h : ℝ) (hh : 0 < h) (j : ℕ) (hj : 2 ≤ j)
    (P : ℝ → ℂ) (hP : Continuous P)
    (M : ℝ) (hM : 0 ≤ M) (hBound : ∀ t, ‖P t‖ ≤ M) :
    (∫ s : ℝ, ∫ t : ℝ, sourceCycleEnergyKernel434 h j P (s,t)) =
      (∫ z : ℝ, collarSchurWeight434 z) *
        (∫ t : ℝ, ((1+h*|t|)^j)⁻¹ * ‖P t‖^2) := by
  have hi := source_cycle_energy_kernel_integrable434
    h hh j hj P hP M hM hBound
  calc
    _ = ∫ t : ℝ, ∫ s : ℝ, sourceCycleEnergyKernel434 h j P (s,t) :=
      integral_integral_swap hi
    _ = ∫ t : ℝ, ((1+h*|t|)^j)⁻¹ *
        (∫ z : ℝ, collarSchurWeight434 z) * ‖P t‖^2 := by
      apply integral_congr_ae
      filter_upwards with t
      exact source_cycle_energy_spatial_row434 h j t P
    _ = (∫ z : ℝ, collarSchurWeight434 z) *
        (∫ t : ℝ, ((1+h*|t|)^j)⁻¹ * ‖P t‖^2) := by
      have he : (fun t : ℝ => ((1+h*|t|)^j)⁻¹ *
          (∫ z : ℝ, collarSchurWeight434 z) * ‖P t‖^2) =
          (fun t : ℝ => (∫ z : ℝ, collarSchurWeight434 z) *
            (((1+h*|t|)^j)⁻¹ * ‖P t‖^2)) := by
        funext t
        ring
      rw [he, integral_const_mul]
end Green64Analytic.CorrelationSquare

end

/-! ## SourceActualLiftOperatorContinuity -/

section

open MeasureTheory
open scoped SchwartzMap
namespace Green64Analytic.CorrelationSquare
set_option maxHeartbeats 1100000

/-- The actual source Fourier-u collar operator maps bounded continuous
Mellin P to a continuous function of the full real cycle frequency s.
Dominating time weight is independent of s, via source IBP and Phi<=1. -/
theorem source_actual_lift_operator_continuous434
    (chi kappa : 𝓢(ℝ,ℂ)) (B : ℝ) (hB : 0 < B)
    (hchi : tsupport (chi : ℝ → ℂ) ⊆ Set.Icc (-B) B)
    (j : ℕ) (hj : 2 ≤ j)
    (h : ℝ) (hh : 0 < h)
    (P : ℝ → ℂ) (hP : Continuous P)
    (M : ℝ) (hM : 0 ≤ M) (hBound : ∀ t, ‖P t‖ ≤ M) :
    Continuous (fun s : ℝ =>
      ∫ t : ℝ, sourceActualCollarLift434 chi kappa h P (s,t)) := by
  obtain ⟨C,hC,hmax⟩ :=
    source_actual_collar_lift_majorant434 chi kappa B hB hchi j
  have hJoint := source_actual_collar_lift_continuous434
    chi kappa B hB hchi h P hP
  let bound : ℝ → ℝ := fun t => (M*C)*((1+h*|t|)^j)⁻¹
  have hInt : Integrable bound :=
    (source_real_time_weight_integrable434 h hh j hj).const_mul (M*C)
  have hMeas (s : ℝ) :
      AEStronglyMeasurable (fun t : ℝ =>
        sourceActualCollarLift434 chi kappa h P (s,t)) := by
    exact (hJoint.comp
      (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  have hDominated (s : ℝ) :
      ∀ᵐ t : ℝ,
        ‖sourceActualCollarLift434 chi kappa h P (s,t)‖ ≤ bound t := by
    apply Filter.Eventually.of_forall
    intro t
    have hkernel :
        sourceCycleMajorant434 h j (s,t) ≤ ((1+h*|t|)^j)⁻¹ := by
      unfold sourceCycleMajorant434
      exact mul_le_of_le_one_right
        (source_collar_real_weight_le_one434 h t hh.le j).1
        (collar_schur_weight_le_one434 _)
    have hcap := hmax h hh P M hM hBound (s,t)
    exact hcap.trans (mul_le_mul_of_nonneg_left hkernel
      (mul_nonneg hM hC.le))
  have hCont (t : ℝ) :
      Continuous (fun s : ℝ =>
        sourceActualCollarLift434 chi kappa h P (s,t)) := by
    exact hJoint.comp (continuous_id.prodMk continuous_const)
  exact continuous_of_dominated hMeas hDominated hInt
    (Filter.Eventually.of_forall hCont)
end Green64Analytic.CorrelationSquare

end

/-! ## SourceActualCollarL2Schur -/

section

open MeasureTheory
open scoped SchwartzMap
namespace Green64Analytic.CorrelationSquare
set_option maxHeartbeats 1450000

/-- FULL source-actual Fourier-side L² Schur operator estimate.
All source h=H/Y>0 and real frequency s, angular time t are quantified.
The whole real line is retained, with genuine absolute Fubini and j>=2.
No unproved high/low/approx/tail or source energy saving is assumed. -/
theorem source_actual_collar_fourier_L2_schur434
    (chi kappa : 𝓢(ℝ,ℂ)) (B : ℝ) (hB : 0 < B)
    (hchi : tsupport (chi : ℝ → ℂ) ⊆ Set.Icc (-B) B)
    (j : ℕ) (hj : 2 ≤ j) :
    ∃ C : ℝ, 0 < C ∧ ∀ (h : ℝ), 0 < h →
      ∀ (P : ℝ → ℂ) (hP : Continuous P)
        (M : ℝ) (hM : 0 ≤ M) (hBound : ∀ t, ‖P t‖ ≤ M),
        Integrable (fun s : ℝ =>
          ‖∫ t : ℝ, sourceActualCollarLift434 chi kappa h P (s,t)‖^2) ∧
        (∫ s : ℝ,
          ‖∫ t : ℝ, sourceActualCollarLift434 chi kappa h P (s,t)‖^2) ≤
          C^2 * (2*Real.pi) *
            (∫ z : ℝ, collarSchurWeight434 z)^2 *
            (∫ t : ℝ, ((1+h*|t|)^j)⁻¹ * ‖P t‖^2) := by
  obtain ⟨C,hC,hpoint⟩ :=
    source_actual_lift_pointwise_energy434 chi kappa B hB hchi j
  refine ⟨C,hC,?_⟩
  intro h hh P hP M hM hBound
  let mass : ℝ := ∫ z : ℝ, collarSchurWeight434 z
  let J : ℝ := (2*Real.pi)*mass
  let D : ℝ := C^2*J
  have hMass : 0 ≤ mass := integral_nonneg
    (fun z => collar_schur_weight_nonneg434 z)
  have hJ : 0 ≤ J := mul_nonneg (by positivity) hMass
  have hD : 0 ≤ D := mul_nonneg (sq_nonneg C) hJ
  have hEnergy := source_cycle_energy_kernel_integrable434
    h hh j hj P hP M hM hBound
  have hRowIntegrable : Integrable (fun s : ℝ =>
      ∫ t : ℝ, sourceCycleEnergyKernel434 h j P (s,t)) :=
    hEnergy.integral_prod_left
  have hCont := source_actual_lift_operator_continuous434
    chi kappa B hB hchi j hj h hh P hP M hM hBound
  have hPoint (s : ℝ) :
      ‖∫ t : ℝ, sourceActualCollarLift434 chi kappa h P (s,t)‖^2 ≤
      D * (∫ t : ℝ, sourceCycleEnergyKernel434 h j P (s,t)) := by
    have hp := hpoint h hh P hP M hM hBound s
    dsimp [D,J,mass,sourceCycleEnergyKernel434]
    simpa only [mul_assoc] using hp
  have hL2Int : Integrable (fun s : ℝ =>
      ‖∫ t : ℝ, sourceActualCollarLift434 chi kappa h P (s,t)‖^2) := by
    apply Integrable.mono' (hRowIntegrable.const_mul D)
      (hCont.norm.pow 2).aestronglyMeasurable
    filter_upwards with s
    change |‖∫ t : ℝ, sourceActualCollarLift434 chi kappa h P (s,t)‖^2| ≤
      D*(∫ t : ℝ, sourceCycleEnergyKernel434 h j P (s,t))
    rw [abs_of_nonneg (sq_nonneg _)]
    exact hPoint s
  refine ⟨hL2Int,?_⟩
  calc
    _ ≤ ∫ s : ℝ, D *
          (∫ t : ℝ, sourceCycleEnergyKernel434 h j P (s,t)) :=
      integral_mono hL2Int (hRowIntegrable.const_mul D) hPoint
    _ = D * (∫ s : ℝ, ∫ t : ℝ,
        sourceCycleEnergyKernel434 h j P (s,t)) := by
      rw [integral_const_mul]
    _ = D * (mass *
        (∫ t : ℝ, ((1+h*|t|)^j)⁻¹ * ‖P t‖^2)) := by
      rw [source_cycle_energy_fubini434 h hh j hj P hP M hM hBound]
    _ = _ := by
      dsimp [D,J]
      ring
end Green64Analytic.CorrelationSquare

end

/-! ## SourceActualL2Plancherel -/

section

open MeasureTheory
open scoped SchwartzMap FourierTransform
namespace Green64Analytic.CorrelationSquare
set_option maxHeartbeats 1000000

/-- The true source Fourier-side lift belongs to L², and its genuine
L² inverse Fourier transform obeys Plancherel. This is NOT yet the
physical identification of that inverse with the original collar Q(u). -/
theorem source_actual_collar_L2_fourier_inverse434
    (chi kappa : 𝓢(ℝ,ℂ)) (B : ℝ) (hB : 0 < B)
    (hchi : tsupport (chi : ℝ → ℂ) ⊆ Set.Icc (-B) B)
    (j : ℕ) (hj : 2 ≤ j) :
    ∃ C : ℝ, 0 < C ∧ ∀ (h : ℝ), 0 < h →
      ∀ (P : ℝ → ℂ) (hP : Continuous P)
        (M : ℝ) (hM : 0 ≤ M) (hBound : ∀ t, ‖P t‖ ≤ M),
        ∃ hLp : MemLp (fun s : ℝ =>
            ∫ t : ℝ, sourceActualCollarLift434 chi kappa h P (s,t))
            2 (volume : Measure ℝ),
          ‖(Lp.fourierTransformₗᵢ ℝ ℂ).symm
            (MemLp.toLp _ hLp)‖ = ‖MemLp.toLp _ hLp‖ ∧
          (∫ s : ℝ,
            ‖∫ t : ℝ, sourceActualCollarLift434 chi kappa h P (s,t)‖^2) ≤
              C^2*(2*Real.pi)*
                (∫ z : ℝ, collarSchurWeight434 z)^2*
                (∫ t : ℝ, ((1+h*|t|)^j)⁻¹*‖P t‖^2) := by
  obtain ⟨C,hC,hL2⟩ :=
    source_actual_collar_fourier_L2_schur434 chi kappa B hB hchi j hj
  refine ⟨C,hC,?_⟩
  intro h hh P hP M hM hBound
  obtain ⟨hInt,hBoundL2⟩ := hL2 h hh P hP M hM hBound
  have hCont := source_actual_lift_operator_continuous434
    chi kappa B hB hchi j hj h hh P hP M hM hBound
  have hLp : MemLp (fun s : ℝ =>
      ∫ t : ℝ, sourceActualCollarLift434 chi kappa h P (s,t))
      2 (volume : Measure ℝ) :=
    (memLp_two_iff_integrable_sq_norm hCont.aestronglyMeasurable).mpr hInt
  refine ⟨hLp, ?_, hBoundL2⟩
  exact (Lp.fourierTransformₗᵢ ℝ ℂ).symm.norm_map (MemLp.toLp _ hLp)
end Green64Analytic.CorrelationSquare

end

/-! ## SourceActualPhysicalTimeIntegral -/

section

open MeasureTheory
open scoped SchwartzMap
namespace Green64Analytic.CorrelationSquare
set_option maxHeartbeats 950000

/-- Actual logarithmic collar before u-Fourier: common angular Mellin phase
exp(-iut), retained compact source center, and the original symbol. -/
noncomputable def sourceActualPhysicalTimeKernel434
    (chi kappa : 𝓢(ℝ,ℂ)) (h : ℝ) (P : ℝ → ℂ) (u t : ℝ) : ℂ :=
  sourceCompactCollarSymbol434 chi kappa h t u *
    Complex.exp (((-(u*t):ℝ):ℂ)*Complex.I) * P t

/-- The original compact source symbol admits a WHOLE-REAL-TIME
majorant uniform in the physical log-center u, including outside support. -/
theorem source_actual_physical_symbol_uniform434
    (chi kappa : 𝓢(ℝ,ℂ)) (B : ℝ) (hB : 0 < B)
    (hchi : tsupport (chi : ℝ → ℂ) ⊆ Set.Icc (-B) B)
    (j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (h : ℝ), 0 < h →
      ∀ (u t : ℝ),
        ‖sourceCompactCollarSymbol434 chi kappa h t u‖ ≤
          C * ((1+h*|t|)^j)⁻¹ := by
  obtain ⟨C,hC,huniform⟩ :=
    source_compact_collar_symbol_uniform434 chi kappa B j
  refine ⟨C,hC,?_⟩
  intro h hh u t
  by_cases hu : |u| ≤ B
  · have hr := huniform h t u hu
    have he : (1+|h*t|)^j = (1+h*|t|)^j := by
      rw [abs_mul, abs_of_pos hh]
    have hp : 0 < (1+h*|t|)^j := by
      have hnn : 0 ≤ h*|t| := mul_nonneg hh.le (abs_nonneg _)
      exact pow_pos (by linarith : 0 < 1+h*|t|) _
    rw [he] at hr
    calc
      _ ≤ C/((1+h*|t|)^j) :=
        (le_div_iff₀ hp).mpr (by
          simpa only [mul_comm] using hr)
      _ = C*((1+h*|t|)^j)⁻¹ := by ring
  · have hOutside : u ∉ Set.Icc (-B) B := by
      intro huI
      exact hu (abs_le.mpr (Set.mem_Icc.mp huI))
    have hz : chi u = 0 := by
      by_contra hn
      exact hOutside (hchi (subset_closure hn))
    simp only [sourceCompactCollarSymbol434, hz, zero_mul, norm_zero]
    positivity

/-- Pointwise true u,t logarithmic physical kernel has the same weighted
time majorant, with no h^{-1} or polynomial-energy premise. -/
theorem source_actual_physical_time_kernel_majorant434
    (chi kappa : 𝓢(ℝ,ℂ)) (B : ℝ) (hB : 0 < B)
    (hchi : tsupport (chi : ℝ → ℂ) ⊆ Set.Icc (-B) B)
    (j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (h : ℝ), 0 < h →
      ∀ (P : ℝ → ℂ) (M : ℝ), 0 ≤ M →
        (∀ t, ‖P t‖ ≤ M) →
        ∀ (u t : ℝ),
          ‖sourceActualPhysicalTimeKernel434 chi kappa h P u t‖ ≤
            (C*M)*((1+h*|t|)^j)⁻¹ := by
  obtain ⟨C,hC,hA⟩ :=
    source_actual_physical_symbol_uniform434 chi kappa B hB hchi j
  refine ⟨C,hC,?_⟩
  intro h hh P M hM hBound u t
  have hphase :
      ‖Complex.exp (((-(u*t):ℝ):ℂ)*Complex.I)‖ = 1 :=
    Complex.norm_exp_ofReal_mul_I _
  calc
    ‖sourceActualPhysicalTimeKernel434 chi kappa h P u t‖ =
      ‖sourceCompactCollarSymbol434 chi kappa h t u‖ * ‖P t‖ := by
      simp only [sourceActualPhysicalTimeKernel434, norm_mul,hphase, mul_one]
    _ ≤ (C*((1+h*|t|)^j)⁻¹)*M :=
      mul_le_mul (hA h hh u t) (hBound t)
        (norm_nonneg _) (mul_nonneg hC.le (by positivity))
    _ = (C*M)*((1+h*|t|)^j)⁻¹ := by ring
end Green64Analytic.CorrelationSquare

end

/-! ## SourceActualPhysicalTimeBochner -/

section

open MeasureTheory
open scoped SchwartzMap
namespace Green64Analytic.CorrelationSquare
set_option maxHeartbeats 700000

/-- The actual full-real angular-time Bochner integrand is integrable
at every physical log-center. The j>=2 hypothesis prevents default-zero. -/
theorem source_actual_physical_time_integrable434
    (chi kappa : 𝓢(ℝ,ℂ)) (B : ℝ) (hB : 0 < B)
    (hchi : tsupport (chi : ℝ → ℂ) ⊆ Set.Icc (-B) B)
    (j : ℕ) (hj : 2 ≤ j) :
    ∀ (h : ℝ), 0 < h →
      ∀ (P : ℝ → ℂ) (hP : Continuous P)
        (M : ℝ) (hM : 0 ≤ M) (hBound : ∀ t, ‖P t‖ ≤ M)
        (u : ℝ),
      Integrable (fun t : ℝ =>
        sourceActualPhysicalTimeKernel434 chi kappa h P u t) := by
  obtain ⟨C,hC,hmajor⟩ :=
    source_actual_physical_time_kernel_majorant434 chi kappa B hB hchi j
  intro h hh P hP M hM hBound u
  have hc : Continuous (fun t : ℝ =>
      sourceActualPhysicalTimeKernel434 chi kappa h P u t) := by
    unfold sourceActualPhysicalTimeKernel434
      sourceCompactCollarSymbol434 collarZ434
    fun_prop
  apply Integrable.mono'
    ((source_real_time_weight_integrable434 h hh j hj).const_mul (C*M))
    hc.aestronglyMeasurable
  filter_upwards with t
  exact hmajor h hh P M hM hBound u t
end Green64Analytic.CorrelationSquare

end

/-! ## SourceActualPhysicalJoint -/

section

open MeasureTheory
open scoped SchwartzMap
namespace Green64Analytic.CorrelationSquare
set_option maxHeartbeats 700000

/-- Joint continuity of the LITERAL u,t physical source integrand;
the unbounded angular time is retained, with original exp(-iut). -/
theorem source_actual_physical_kernel_joint_continuous434
    (chi kappa : 𝓢(ℝ,ℂ)) (h : ℝ) (P : ℝ → ℂ) (hP : Continuous P) :
    Continuous (fun p : ℝ × ℝ =>
      sourceActualPhysicalTimeKernel434 chi kappa h P p.1 p.2) := by
  have hc : Continuous (fun p : ℝ × ℝ => chi p.1) :=
    chi.continuous.comp continuous_fst
  have he : Continuous (fun p : ℝ × ℝ => (Real.exp (-p.1) : ℂ)) := by
    fun_prop
  have hz : Continuous (fun p : ℝ × ℝ =>
      collarZ434 h p.2 p.1) := by
    unfold collarZ434
    fun_prop
  have hk : Continuous (fun p : ℝ × ℝ =>
      kappa (collarZ434 h p.2 p.1)) :=
    kappa.continuous.comp hz
  have hphase : Continuous (fun p : ℝ × ℝ =>
      Complex.exp (((-(p.1*p.2):ℝ):ℂ)*Complex.I)) := by
    fun_prop
  have hcp : Continuous (fun p : ℝ × ℝ => P p.2) :=
    hP.comp continuous_snd
  change Continuous (fun p : ℝ × ℝ =>
    chi p.1 * (Real.exp (-p.1) : ℂ) *
      kappa (collarZ434 h p.2 p.1) *
      Complex.exp (((-(p.1*p.2):ℝ):ℂ)*Complex.I) * P p.2)
  exact (((hc.mul he).mul hk).mul hphase).mul hcp
end Green64Analytic.CorrelationSquare

end

/-! ## SourceActualPhysicalQDef -/

section

open MeasureTheory
open scoped SchwartzMap
namespace Green64Analytic.CorrelationSquare
/-- The genuine original physical compact log-center collar. -/
noncomputable def sourceActualPhysicalQ434
    (chi kappa : 𝓢(ℝ,ℂ)) (h : ℝ) (P : ℝ → ℂ) (u : ℝ) : ℂ :=
  ∫ t : ℝ, sourceActualPhysicalTimeKernel434 chi kappa h P u t
end Green64Analytic.CorrelationSquare

end

