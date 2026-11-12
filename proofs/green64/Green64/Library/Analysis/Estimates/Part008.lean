module

public import Green64.Library.Weights.SourceD27LengthSplit
public import Green64.Library.Weights.Part012
public import Green64.Library.Sieve.Foundation.Lemma9.Part005
public import Green64.Library.Weights.Part036
public import Green64.Library.Analysis.Estimates.Part006
public import Green64.Library.Analysis.Estimates.Part003
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

@[expose] public section

/-!
# Analysis / Estimates / Part008

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceD27PrimeLayer -/

section

open Filter Topology
open scoped BigOperators Classical
namespace Green64Analytic.SourceBlockSieve
set_option maxHeartbeats 0
set_option autoImplicit false

theorem sourceD27_one_prime_tuple_le_prime_count
    (Y Δ y : ℝ) (hY : 0≤Y) :
    ((sourceD24OrderedCellTuples 1 Y Δ y).card:ℝ) ≤
      sourceD22PrimeCount Y Δ := by
  let T := sourceD24OrderedCellTuples 1 Y Δ y
  let P := (sourceD22Cell Y Δ).filter Nat.Prime
  have hmap : Set.MapsTo (fun l : List ℕ => l.head!) (↑T) (↑P) := by
    intro l hl
    obtain ⟨hAll,hlo⟩ := Finset.mem_filter.mp hl
    have hZ : 0≤Real.exp Δ*Y := mul_nonneg (Real.exp_pos _).le hY
    have hinfo := (Green64Analytic.OrderedPrimeRough.mem_allPrimeTuples_iff
      1 y (Real.exp Δ*Y) hZ l).mp hAll
    have hh : ∃ p, l=[p] := by
      rcases l with _ | ⟨p,t⟩
      · simp at hinfo
      · cases t with
        | nil => exact ⟨p,rfl⟩
        | cons q t => simp at hinfo
    obtain ⟨p,rfl⟩ := hh
    have hp := (hinfo.2.1 p (by simp)).1
    have hpY : Y<(p:ℝ) := by simpa using hlo
    have hpZ : (p:ℝ)≤Real.exp Δ*Y := by simpa using hinfo.2.2.2
    apply Finset.mem_filter.mpr
    constructor
    · apply Finset.mem_Ioc.mpr
      exact ⟨(Nat.floor_lt hY).mpr hpY,Nat.le_floor hpZ⟩
    · exact hp
  have hinj : Set.InjOn (fun l : List ℕ => l.head!) (↑T) := by
    intro a ha b hb he
    have haI := (Green64Analytic.OrderedPrimeRough.mem_allPrimeTuples_iff
      1 y (Real.exp Δ*Y) (mul_nonneg (Real.exp_pos _).le hY) a).mp
      (Finset.mem_filter.mp ha).1
    have hbI := (Green64Analytic.OrderedPrimeRough.mem_allPrimeTuples_iff
      1 y (Real.exp Δ*Y) (mul_nonneg (Real.exp_pos _).le hY) b).mp
      (Finset.mem_filter.mp hb).1
    rcases a with _ | ⟨p,t⟩
    · simp at haI
    · cases t with
      | nil =>
        rcases b with _ | ⟨q,s⟩
        · simp at hbI
        · cases s with
          | nil => simpa using he
          | cons u s => simp at hbI
      | cons q t => simp at haI
  change (T.card:ℝ) ≤ (P.card:ℝ)
  exact_mod_cast Finset.card_le_card_of_injOn (fun l : List ℕ => l.head!) hmap hinj


end Green64Analytic.SourceBlockSieve

end

/-! ## SourceD27PrimeAsymptotic -/

section

open Filter Topology
open scoped BigOperators Classical
namespace Green64Analytic.SourceBlockSieve
set_option maxHeartbeats 0
set_option autoImplicit false

/-- Sharp one-prime ordered-tuple cell estimate, using the already
checked exact comparison to the native prime count and the PNT. -/
theorem sourceD27_one_prime_length_upper
    (S b w ε : ℝ) (hS : 0<S) (hb : 0<b)
    (hbw : b<w) (hε : 0<ε) :
    ∀ᶠ L : ℝ in atTop,
      ((sourceD24OrderedCellTuples 1 (Real.exp (w*L))
        (L^(-S)) ((Real.exp L)^b)).card:ℝ) ≤
      ((Real.exp (L^(-S))-1)*Real.exp (w*L))/L *
        (1/w+ε) := by
  have hw : 0<w := hb.trans hbw
  have hεw : 0<ε*w := mul_pos hε hw
  filter_upwards [sourceD22_prime_cell_upper S b (ε*w) hS hb hεw,
    eventually_gt_atTop (0:ℝ)] with L hPNT hL
  have hY : Real.exp (b*L)≤Real.exp (w*L) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hbw.le hL.le)
  have hord := sourceD27_one_prime_tuple_le_prime_count
    (Real.exp (w*L)) (L^(-S)) ((Real.exp L)^b)
    (Real.exp_pos _).le
  have hcount := hPNT (Real.exp (w*L)) hY
  have hlog : Real.log (Real.exp (w*L))=w*L := Real.log_exp _
  have hcoeff :
      (1+ε*w)*(Real.exp (L^(-S))-1)*Real.exp (w*L) / (w*L) =
      ((Real.exp (L^(-S))-1)*Real.exp (w*L))/L*(1/w+ε) := by
    field_simp [hw.ne',hL.ne']
  rw [hlog,hcoeff] at hcount
  exact hord.trans hcount


end Green64Analytic.SourceBlockSieve

end

/-! ## SourceD28UniformPrimeLayer -/

section

open Filter Topology
open scoped BigOperators Classical
namespace Green64Analytic.SourceBlockSieve
set_option maxHeartbeats 0
set_option autoImplicit false

/-- One PNT threshold and original full-cell prime tuple count
uniform over every cofactor exponent in a compact source range. -/
theorem sourceD28_uniform_one_prime_length_upper
    (S b A B ε : ℝ) (hS : 0<S) (hb : 0<b)
    (hbA : b<A) (hε : 0<ε) :
    ∀ᶠ L : ℝ in atTop, ∀ w∈Set.Icc A B,
      ((sourceD24OrderedCellTuples 1 (Real.exp (w*L))
        (L^(-S)) ((Real.exp L)^b)).card:ℝ) ≤
      ((Real.exp (L^(-S))-1)*Real.exp (w*L))/L *
        (1/w+ε) := by
  have hA : 0<A := hb.trans hbA
  have hεA : 0<ε*A := mul_pos hε hA
  filter_upwards [sourceD22_prime_cell_upper S b (ε*A) hS hb hεA,
    eventually_gt_atTop (0:ℝ)] with L hPNT hL
  intro w hw
  have hw0 : 0<w := hA.trans_le hw.1
  have hY : Real.exp (b*L)≤Real.exp (w*L) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (hbA.le.trans hw.1) hL.le)
  have hord := sourceD27_one_prime_tuple_le_prime_count
    (Real.exp (w*L)) (L^(-S)) ((Real.exp L)^b)
    (Real.exp_pos _).le
  have hcount := hPNT (Real.exp (w*L)) hY
  have hlog : Real.log (Real.exp (w*L))=w*L := Real.log_exp _
  have hH : 0≤(Real.exp (L^(-S))-1)*Real.exp (w*L) := by
    exact mul_nonneg (sub_nonneg.mpr (Real.one_le_exp
      (Real.rpow_nonneg hL.le _))) (Real.exp_pos _).le
  have hcoef : (1+ε*A)/(w*L)≤(1/w+ε)/L := by
    have hcore : ε*A≤ε*w :=
      mul_le_mul_of_nonneg_left hw.1 hε.le
    have h1 : (1+ε*A)/(w*L) ≤ (1+ε*w)/(w*L) :=
      div_le_div_of_nonneg_right (by linarith) (mul_pos hw0 hL).le
    have heq : (1+ε*w)/(w*L) = (1/w+ε)/L := by
      field_simp [hw0.ne',hL.ne']
    exact h1.trans_eq heq
  have hnum := mul_le_mul_of_nonneg_left hcoef hH
  have hrewrite : ((1+ε*A)*(Real.exp (L^(-S))-1)*Real.exp (w*L))/(w*L) =
       ((Real.exp (L^(-S))-1)*Real.exp (w*L))*((1+ε*A)/(w*L)) := by ring
  have hrewrite2 : (((Real.exp (L^(-S))-1)*Real.exp (w*L))/L)*(1/w+ε) =
       ((Real.exp (L^(-S))-1)*Real.exp (w*L))*((1/w+ε)/L) := by ring
  rw [hlog] at hcount
  calc
    _ ≤ sourceD22PrimeCount (Real.exp (w*L)) (L^(-S)) := hord
    _ ≤ ((1+ε*A)*(Real.exp (L^(-S))-1)*Real.exp (w*L))/(w*L) := hcount
    _ = ((Real.exp (L^(-S))-1)*Real.exp (w*L))*((1+ε*A)/(w*L)) := hrewrite
    _ ≤ ((Real.exp (L^(-S))-1)*Real.exp (w*L))*((1/w+ε)/L) := hnum
    _ = _ := hrewrite2.symm


end Green64Analytic.SourceBlockSieve

end

/-! ## SourceD27FiniteAllLayers -/

section

open Filter Topology
open scoped BigOperators Classical
namespace Green64Analytic.SourceBlockSieve
set_option maxHeartbeats 0
set_option autoImplicit false

/-- All fixed actual full-cell prime-factor lengths, including the
empty and single-prime lengths, retain one common epsilon budget. -/
theorem sourceD27_all_finite_layers_upper
    (K : ℕ) (S b w ε : ℝ)
    (hS : 0<S) (hb : 0<b) (hbw : b<w) (hw1 : w<1) (hε : 0<ε) :
    ∀ᶠ L : ℝ in atTop,
      (∑ ell∈Finset.range (K+2),
        ((sourceD24OrderedCellTuples ell (Real.exp (w*L))
            (L^(-S)) ((Real.exp L)^b)).card:ℝ) /
          (ell.factorial:ℝ)) ≤
      (((Real.exp (L^(-S))-1)*Real.exp (w*L))/L) *
        (1/w + (∑ n∈Finset.range K,
          Green64Analytic.SmallB.sourceSimplexTerm n b w) + ε) := by
  let η : ℝ := ε / ((K+1:ℕ):ℝ)
  have hKn : (0:ℝ)<((K+1:ℕ):ℝ) := by positivity
  have hη : 0<η := div_pos hε hKn
  have hp := sourceD27_one_prime_length_upper S b w η hS hb hbw hη
  have hc : ∀ᶠ L : ℝ in atTop, ∀ n∈Finset.range K,
      ((sourceD24OrderedCellTuples (n+2) (Real.exp (w*L))
        (L^(-S)) ((Real.exp L)^b)).card:ℝ)/
        ((n+2).factorial:ℝ) ≤
      (((Real.exp (L^(-S))-1)*Real.exp (w*L))/L) *
        (Green64Analytic.SmallB.sourceSimplexTerm n b w+η) := by
    rw [Filter.eventually_all_finset]
    intro n hn
    exact sourceD27_higher_length_cell_upper n S b w η
      hS hb hbw hw1 hη
  filter_upwards [hp,hc,eventually_gt_atTop (0:ℝ)] with L hprime hcomp hL
  let H : ℝ := ((Real.exp (L^(-S))-1)*Real.exp (w*L))/L
  have hY : 1≤Real.exp (w*L) :=
    Real.one_le_exp (mul_nonneg (hb.trans hbw).le hL.le)
  have hsplit := sourceD27_length_sum_split K (Real.exp (w*L))
    (L^(-S)) ((Real.exp L)^b) hY
  have hcompsum : (∑ n∈Finset.range K,
      ((sourceD24OrderedCellTuples (n+2) (Real.exp (w*L))
        (L^(-S)) ((Real.exp L)^b)).card:ℝ)/
        ((n+2).factorial:ℝ)) ≤
      H*(∑ n∈Finset.range K,
        (Green64Analytic.SmallB.sourceSimplexTerm n b w+η)) := by
    calc
      _ ≤ ∑ n∈Finset.range K,
          H*(Green64Analytic.SmallB.sourceSimplexTerm n b w+η) :=
        Finset.sum_le_sum hcomp
      _ = _ := by rw [Finset.mul_sum]
  have hepsilon : (((K+1:ℕ):ℝ)*η)=ε :=
    mul_div_cancel₀ ε hKn.ne'
  have herr : η+(K:ℝ)*η=ε := by
    calc
      _ = ((K+1:ℕ):ℝ)*η := by push_cast; ring
      _ = ε := hepsilon
  rw [hsplit]
  have heq : (∑ n∈Finset.range K,
      (Green64Analytic.SmallB.sourceSimplexTerm n b w+η)) =
      (∑ n∈Finset.range K,
        Green64Analytic.SmallB.sourceSimplexTerm n b w)+(K:ℝ)*η := by
    rw [Finset.sum_add_distrib]
    simp
  calc
    _ ≤ H*(1/w+η) + H*(∑ n∈Finset.range K,
        (Green64Analytic.SmallB.sourceSimplexTerm n b w+η)) :=
      add_le_add hprime hcompsum
    _ = H*(1/w + (∑ n∈Finset.range K,
        Green64Analytic.SmallB.sourceSimplexTerm n b w) + ε) := by
      rw [heq]
      calc
        H*(1/w+η)+H*((∑ n∈Finset.range K,
          Green64Analytic.SmallB.sourceSimplexTerm n b w)+(K:ℝ)*η) =
        H*(1/w+(∑ n∈Finset.range K,
          Green64Analytic.SmallB.sourceSimplexTerm n b w)+(η+(K:ℝ)*η)) := by ring
        _ = _ := by rw [herr]


end Green64Analytic.SourceBlockSieve

end

/-! ## SourceD27ExactRepeatedUpper -/

section

open Filter Topology
open scoped BigOperators Classical
namespace Green64Analytic.SourceBlockSieve
set_option maxHeartbeats 0
set_option autoImplicit false

/-- Retain the exact repeated-factor count, rather than the earlier
crude 2 exp(Delta)Y/(floor(y)+1) error, in the full rough numerator. -/
theorem sourceD27_full_rough_exact_repeated
    (K : ℕ) (Y Δ y : ℝ) (hY : 0≤Y) (hy : 1≤y)
    (hcut : Real.exp Δ*Y≤y^(K+1)) :
    sourceD22Count Y Δ y ≤
      (∑ ell∈Finset.range (K+1),
        ((sourceD24OrderedCellTuples ell Y Δ y).card:ℝ)/
          (ell.factorial:ℝ)) +
      ((sourceD24RepeatedCell Y Δ y).card:ℝ) := by
  let C := (sourceD22Cell Y Δ).filter (sourceD20Rough y)
  have hsplit := Finset.card_filter_add_card_filter_not (s:=C) Squarefree
  have hsq : C.filter Squarefree = sourceD24SquarefreeCell Y Δ y := by
    ext n
    simp only [C,sourceD24SquarefreeCell,Finset.mem_filter]
    tauto
  have hrep : C.filter (fun n => ¬Squarefree n)=sourceD24RepeatedCell Y Δ y := by
    ext n
    simp only [C,sourceD24RepeatedCell,Finset.mem_filter]
    tauto
  rw [hsq,hrep] at hsplit
  have heq : sourceD22Count Y Δ y =
      ((sourceD24SquarefreeCell Y Δ y).card:ℝ)+
      ((sourceD24RepeatedCell Y Δ y).card:ℝ) := by
    change (C.card:ℝ)=_
    exact_mod_cast hsplit.symm
  rw [heq]
  simpa only [add_comm] using
    (add_le_add_right (sourceD24_squarefree_ordered_upper K Y Δ y hY hy hcut)
      ((sourceD24RepeatedCell Y Δ y).card:ℝ))


end Green64Analytic.SourceBlockSieve

end

/-! ## SourceD27DensityCutoff -/

section

open Filter Topology
open scoped BigOperators Classical
namespace Green64Analytic.SourceBlockSieve
set_option maxHeartbeats 0
set_option autoImplicit false

/-- A predetermined finite length budget dominates the true full-cell
upper endpoint, even when the logarithmic mesh moves with L. -/
theorem sourceD27_fixed_exponent_cutoff
    (K : ℕ) (S b w : ℝ) (hS : 0<S) (hb : 0<b)
    (hgap : w < b*((K+2:ℕ):ℝ)) :
    ∀ᶠ L : ℝ in atTop,
      Real.exp (L^(-S))*Real.exp (w*L) ≤ ((Real.exp L)^b)^(K+2) := by
  have _ := hb
  let q := b*((K+2:ℕ):ℝ)-w
  have hq : 0<q := sub_pos.mpr hgap
  filter_upwards [eventually_ge_atTop (max 1 (1/q))] with L hlarge
  have hL1 : 1≤L := (le_max_left _ _).trans hlarge
  have hL : 0<L := by linarith
  have hqL : 1≤q*L := by
    have hh := (div_le_iff₀ hq).mp ((le_max_right _ _).trans hlarge)
    linarith
  have hmesh : L^(-S)≤1 := by
    simpa only [Real.rpow_zero] using
      Real.rpow_le_rpow_of_exponent_le hL1 (show -S≤0 by linarith)
  have hright : ((Real.exp L)^b)^(K+2) =
      Real.exp (b*((K+2:ℕ):ℝ)*L) := by
    rw [Real.rpow_def_of_pos (Real.exp_pos L),Real.log_exp]
    rw [←Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [hright]
  calc
    Real.exp (L^(-S))*Real.exp (w*L) =
      Real.exp (L^(-S)+w*L) := (Real.exp_add _ _).symm
    _ ≤ Real.exp (b*((K+2:ℕ):ℝ)*L) :=
      Real.exp_le_exp.mpr (by dsimp [q] at hqL; linarith)

theorem sourceD27_finite_density_identity
    (K : ℕ) (b w : ℝ) (hb : 0<b)
    (hcut : w ≤ ((K+2:ℕ):ℝ)*b) :
    1/w + (∑ n∈Finset.range K,
      Green64Analytic.SmallB.sourceSimplexTerm n b w) =
        Green64Analytic.SmallB.sourceDensity b w := by
  have hfinite := Green64Analytic.ReciprocalSimplex.density_finite_cutoff
    K b w hb.le hcut
  change (∑' n : ℕ, Green64Analytic.SmallB.sourceSimplexTerm n b w) =
      ∑ n∈Finset.range K, Green64Analytic.SmallB.sourceSimplexTerm n b w at hfinite
  unfold Green64Analytic.SmallB.sourceDensity
  rw [hfinite]



end Green64Analytic.SourceBlockSieve

end

/-! ## SourceD28BandShift -/

section

open Filter Topology MeasureTheory
open scoped BigOperators Classical
namespace Green64Analytic.SourceBlockSieve
set_option maxHeartbeats 0
set_option autoImplicit false

open Green64Analytic.SourceSimplexGeometry

/-- Arithmetic of moving the center of the actual source
last-prime collar. No assumptions on its width or sign. -/
theorem sourceD28_band_shift_subset
    (d : ℕ) (b w v δ ρ : ℝ)
    (hwv : |w-v| ≤ ρ) :
    sourceD26BoundaryBand d b w δ ⊆
      sourceD26BoundaryBand d b v (δ+ρ) := by
  intro t ht
  obtain ⟨hc, hlo, hhi⟩ := ht
  have ⟨hneg,hpos⟩ := abs_le.mp hwv
  change (∀ i, b ≤ t i) ∧ v-b-(δ+ρ) < (∑ i, t i) ∧ (∑ i, t i) ≤ v-b+(δ+ρ)
  refine ⟨hc,?_,?_⟩
  · linarith
  · linarith

/-- Monotonicity of the TRUE reciprocal-prime continuum collar integral
under any explicit inclusion, without an extra distribution premise. -/
theorem sourceD28_band_integral_mono
    (d : ℕ) (b w v δ η : ℝ)
    (hb : 0<b)
    (hsub : sourceD26BoundaryBand d b w δ ⊆
      sourceD26BoundaryBand d b v η) :
    (∫ t in sourceD26BoundaryBand d b w δ,
      reciprocalProduct d t) ≤
    (∫ t in sourceD26BoundaryBand d b v η,
      reciprocalProduct d t) := by
  let A := sourceD26BoundaryBand d b w δ
  let B := sourceD26BoundaryBand d b v η
  have hBout : B ⊆ sourceRegion d b (v+η) := by
    intro t ht
    exact ⟨ht.1,by linarith [ht.2.2]⟩
  have hint : IntegrableOn (reciprocalProduct d) B :=
    (reciprocalProduct_integrableOn_source d b (v+η) hb).mono_set hBout
  have hnonneg :
      0 ≤ᵐ[(volume : Measure (Fin d → ℝ)).restrict B]
        reciprocalProduct d := by
    filter_upwards [ae_restrict_mem (sourceD26_band_measurable d b v η)]
      with t ht
    unfold reciprocalProduct
    exact Finset.prod_nonneg
      (fun i hi => inv_nonneg.mpr (hb.le.trans (ht.1 i)))
  exact setIntegral_mono_set hint hnonneg (Filter.Eventually.of_forall hsub)

/-- The band-integral comparison when centers differ by at most ρ. -/
theorem sourceD28_band_integral_shift
    (d : ℕ) (b w v δ ρ : ℝ)
    (hb : 0<b) (hwv : |w-v|≤ρ) :
    (∫ t in sourceD26BoundaryBand d b w δ,
      reciprocalProduct d t) ≤
    (∫ t in sourceD26BoundaryBand d b v (δ+ρ),
      reciprocalProduct d t) :=
  sourceD28_band_integral_mono d b w v δ (δ+ρ) hb
    (sourceD28_band_shift_subset d b w v δ ρ hwv)


end Green64Analytic.SourceBlockSieve

end

