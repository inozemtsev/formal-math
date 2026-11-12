module

public import Green64.Library.Sieve.Foundation.Lemma9.Part005
public import Green64.Library.Weights.Part012
public import Green64.Library.Analysis.Estimates.PrimeFineProxy
public import Green64.Library.Analysis.Estimates.Part005
public import Mathlib.Analysis.PSeries
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Green64.Library.Weights.Part022
public import Mathlib.Data.Nat.Squarefree
public import Green64.Library.Analysis.Estimates.Part001
public import Green64.Library.Weights.Part021
public import Green64.Library.Weights.Part023
public import Green64.Library.Correlation.Part002
public import Mathlib

@[expose] public section

/-!
# Analysis / Estimates / Part006

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## ActualPrimeDensity -/

section

open Filter Topology
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.SourceBlockSieve
set_option autoImplicit false
set_option maxHeartbeats 8000000

/-- Positive and asymptotically normalized denominator on the complete
cell containing the actual integer, including cells cut by a test interval. -/
theorem b631_actual_full_cell_denominator434
    (S β ε : ℝ) (hS : 0 < S) (hβ : 0 < β) (hε : 0 < ε) :
    ∀ᶠ L : ℝ in atTop, ∀ n : ℕ,
      Real.exp (β * L) ≤ (n : ℝ) →
      let j := sourceD20CellIndex (L ^ (-S)) n
      let C := sourceD20LogCell (L ^ (-S)) j
      let Y := Real.exp ((j : ℝ) * L ^ (-S))
      let V := sourceNaturalEuler ⌊Real.exp (Real.sqrt L)⌋₊
      let den := ((C.filter (sourceD20Rough (Real.exp (Real.sqrt L)))).card : ℝ)
      0 < den ∧ |den / ((Real.exp (L ^ (-S)) - 1) * Y * V) - 1| ≤ ε := by
  filter_upwards [sourceD22_actual_log_denominator S β ε hS hβ hε,
    eventually_gt_atTop (0 : ℝ)] with L hden hL
  intro n hn
  have hn1 : (1 : ℝ) < n :=
    (Real.one_lt_exp_iff.mpr (mul_pos hβ hL)).trans_le hn
  have hn2 : 2 ≤ n := by
    have : 1 < n := by exact_mod_cast hn1
    omega
  exact hden _ ⟨n, sourceD20_index_mem (Real.rpow_pos_of_pos hL _) n hn2, hn⟩

/-- The literal prime numerator divided by the actual W-rough full-cell
normalizer has the sharp PNT density; no density premise is supplied. -/
theorem b631_actual_prime_full_cell_ratio434
    (S β ε : ℝ) (hS : 0 < S) (hβ : 0 < β) (hε : 0 < ε) :
    ∀ᶠ L : ℝ in atTop, ∀ Y : ℝ,
      Real.exp (β * L) ≤ Y →
      sourceD22PrimeCount Y (L ^ (-S)) /
        sourceD22Count Y (L ^ (-S)) (Real.exp (Real.sqrt L)) ≤
      (1 + ε) / (Real.log Y * sourceNaturalEuler ⌊Real.exp (Real.sqrt L)⌋₊) := by
  let δ := min (1 / 2 : ℝ) (ε / 4)
  have hδ : 0 < δ := lt_min (by norm_num) (by linarith)
  have hδ1 : δ ≤ 1 / 2 := min_le_left _ _
  have hδε : δ ≤ ε / 4 := min_le_right _ _
  have hcoef : 1 + δ ≤ (1 + ε) * (1 - δ) := by nlinarith
  filter_upwards [sourceD22_prime_cell_upper S β δ hS hβ hδ,
    sourceD22_denominator_relative S β δ hβ hδ,
    sourceD22_denominator_positive S β hβ,
    eventually_gt_atTop (0 : ℝ)] with L hnum hden hpos hL
  intro Y hY
  let H := (Real.exp (L ^ (-S)) - 1) * Y
  let V := sourceNaturalEuler ⌊Real.exp (Real.sqrt L)⌋₊
  let N := sourceD22PrimeCount Y (L ^ (-S))
  let T := sourceD22Count Y (L ^ (-S)) (Real.exp (Real.sqrt L))
  have hY1 : 1 < Y := (Real.one_lt_exp_iff.mpr (mul_pos hβ hL)).trans_le hY
  have hl : 0 < Real.log Y := Real.log_pos hY1
  have hH : 0 < H := mul_pos
    (sub_pos.mpr (Real.one_lt_exp_iff.mpr (Real.rpow_pos_of_pos hL _)))
    (by linarith)
  have hV : 0 < V := (inv_pos.mpr (Real.exp_pos _)).trans_le
    (sourceD22_euler_lower _ (Real.one_le_exp (Real.sqrt_nonneg L)))
  have hT : 0 < T := hpos Y hY
  have hN : N * Real.log Y ≤ (1 + δ) * H := by
    have hh := (le_div_iff₀ hl).mp (hnum Y hY)
    simpa only [N, H, mul_assoc] using hh
  have hTlower : (1 - δ) * H * V ≤ T := by
    have hh := (abs_le.mp (hden Y hY)).1
    change -(δ * (H * V)) ≤ T - H * V at hh
    nlinarith only [hh]
  change N / T ≤ (1 + ε) / (Real.log Y * V)
  apply (div_le_div_iff₀ hT (mul_pos hl hV)).mpr
  calc
    N * (Real.log Y * V) = (N * Real.log Y) * V := by ring
    _ ≤ ((1 + δ) * H) * V := mul_le_mul_of_nonneg_right hN hV.le
    _ ≤ (((1 + ε) * (1 - δ)) * H) * V := by gcongr
    _ = (1 + ε) * ((1 - δ) * H * V) := by ring
    _ ≤ (1 + ε) * T := mul_le_mul_of_nonneg_left hTlower (by linarith)

/-- Sharp density for the literal prime proxy at every integer above a
fixed positive power of exp L; the whole original logarithmic cell is retained. -/
theorem b631_actual_prime_fine_proxy_density434
    (S β ε : ℝ) (hS : 0 < S) (hβ : 0 < β) (hε : 0 < ε) :
    ∀ᶠ L : ℝ in atTop, ∀ n : ℕ,
      Real.exp (β * L) ≤ (n : ℝ) →
      b627PrimeFullProxy434 (L ^ (-S)) (Real.exp (Real.sqrt L)) n ≤
      (1 + ε) / (Real.log (n : ℝ) * sourceNaturalEuler ⌊Real.exp (Real.sqrt L)⌋₊) := by
  let δ := min (1 / 2 : ℝ) (ε / 4)
  have hδ : 0 < δ := lt_min (by norm_num) (by linarith)
  have hδ1 : δ ≤ 1 / 2 := min_le_left _ _
  have hδε : δ ≤ ε / 4 := min_le_right _ _
  have hcoef : (1 + δ) ^ 2 ≤ 1 + ε := by nlinarith only [hδ1,hδε,hδ]
  filter_upwards [b631_actual_prime_full_cell_ratio434 S (β / 2) δ hS (by linarith) hδ,
    sourceD22_cell_lower S β hS hβ,
    eventually_ge_atTop (max 1 (2 / (δ * β)))] with L hratio hlower hL
  have hL1 : 1 ≤ L := (le_max_left _ _).trans hL
  have hLpos : 0 < L := by linarith
  have hLlarge : 2 / (δ * β) ≤ L := (le_max_right _ _).trans hL
  have hDelta : 0 < L ^ (-S) := Real.rpow_pos_of_pos hLpos _
  have hmesh : L ^ (-S) ≤ 1 := by
    simpa only [Real.rpow_zero] using Real.rpow_le_rpow_of_exponent_le hL1
      (show -S ≤ 0 by linarith)
  intro n hnl
  have hn1 : (1 : ℝ) < n := (Real.one_lt_exp_iff.mpr (mul_pos hβ hLpos)).trans_le hnl
  have hn2 : 2 ≤ n := by
    have hh : 1 < n := by exact_mod_cast hn1
    omega
  let j := sourceD20CellIndex (L ^ (-S)) n
  let Y := Real.exp ((j : ℝ) * L ^ (-S))
  let V := sourceNaturalEuler ⌊Real.exp (Real.sqrt L)⌋₊
  let v := b627PrimeFullProxy434 (L ^ (-S)) (Real.exp (Real.sqrt L)) n
  have hcell := sourceD20_index_mem hDelta n hn2
  have hYlow : Real.exp ((β / 2) * L) ≤ Y := hlower j n hcell hnl
  have hY1 : 1 < Y := (Real.one_lt_exp_iff.mpr (mul_pos (by linarith) hLpos)).trans_le hYlow
  have hlogY : 0 < Real.log Y := Real.log_pos hY1
  have hV : 0 < V := (inv_pos.mpr (Real.exp_pos _)).trans_le
    (sourceD22_euler_lower _ (Real.one_le_exp (Real.sqrt_nonneg L)))
  have hcap := hratio Y hYlow
  have hv0 : 0 ≤ v := by
    dsimp [v, b627PrimeFullProxy434]
    split_ifs <;> positivity
  have hv : v ≤ (1 + δ) / (Real.log Y * V) := by
    dsimp [v, b627PrimeFullProxy434]
    rw [sourceD22_log_cell_exact]
    split_ifs
    · simpa only [sourceD22PrimeCount, sourceD22Count, Y, j, V] using hcap
    · positivity
  have hvY : v * (Real.log Y * V) ≤ 1 + δ := (le_div_iff₀ (mul_pos hlogY hV)).mp hv
  have hlnlow : (β / 2) * L ≤ Real.log Y := by
    have hh := Real.log_le_log (Real.exp_pos _) hYlow
    simpa only [Real.log_exp] using hh
  have hlnup : Real.log (n : ℝ) ≤ Real.log Y + L ^ (-S) := by
    have hh := (sourceD20_mem_cell _ j n).mp hcell
    have hl := (Real.log_le_iff_le_exp (by linarith : (0 : ℝ) < n)).mpr hh.2
    simpa only [Y, Real.log_exp, add_mul, one_mul] using hl
  have hbudget : L ^ (-S) ≤ δ * Real.log Y := by
    have hh := (div_le_iff₀ (mul_pos hδ hβ)).mp hLlarge
    have hmul := mul_le_mul_of_nonneg_left hlnlow hδ.le
    nlinarith only [hh, hmul, hmesh]
  have hlogs : Real.log (n : ℝ) ≤ (1 + δ) * Real.log Y := by linarith
  have hmul := mul_le_mul_of_nonneg_left hlogs (mul_nonneg hv0 hV.le)
  have hscaled : v * (Real.log (n : ℝ) * V) ≤ (1 + δ) ^ 2 := by
    calc
      _ ≤ (1 + δ) * (v * (Real.log Y * V)) := by nlinarith only [hmul]
      _ ≤ (1 + δ) * (1 + δ) := mul_le_mul_of_nonneg_left hvY (by linarith)
      _ = _ := by ring
  apply (le_div_iff₀ (mul_pos (Real.log_pos hn1) hV)).mpr
  exact hscaled.trans hcoef

/-- The coefficient density constant 3 is independent of the later fine
precision S. This window contains Parity's actual balanced prime-factor range. -/
theorem b631_actual_prime_fine_density_uniform_constant434
    (S : ℝ) (hS : 0 < S) :
    ∀ᶠ L : ℝ in atTop, ∀ n : ℕ,
      Real.exp ((2 / 5 : ℝ) * L) ≤ (n : ℝ) →
      0 ≤ b627PrimeFullProxy434 (L ^ (-S)) (Real.exp (Real.sqrt L)) n ∧
      b627PrimeFullProxy434 (L ^ (-S)) (Real.exp (Real.sqrt L)) n ≤
        3 / (L * sourceNaturalEuler ⌊Real.exp (Real.sqrt L)⌋₊) := by
  filter_upwards [b631_actual_prime_fine_proxy_density434 S (2 / 5) (1 / 5)
    hS (by norm_num) (by norm_num), eventually_gt_atTop (0 : ℝ)] with L hd hL
  intro n hn
  have hv0 : 0 ≤ b627PrimeFullProxy434 (L ^ (-S)) (Real.exp (Real.sqrt L)) n := by
    unfold b627PrimeFullProxy434
    split_ifs <;> positivity
  refine ⟨hv0, (hd n hn).trans ?_⟩
  have hn1 : (1 : ℝ) < n :=
    (Real.one_lt_exp_iff.mpr (mul_pos (by norm_num : (0 : ℝ) < 2 / 5) hL)).trans_le hn
  have hlog : (2 / 5 : ℝ) * L ≤ Real.log (n : ℝ) := by
    have hh := Real.log_le_log (Real.exp_pos _) hn
    simpa only [Real.log_exp] using hh
  have hV : 0 < sourceNaturalEuler ⌊Real.exp (Real.sqrt L)⌋₊ :=
    (inv_pos.mpr (Real.exp_pos _)).trans_le
      (sourceD22_euler_lower _ (Real.one_le_exp (Real.sqrt_nonneg L)))
  apply (div_le_div_iff₀ (mul_pos (Real.log_pos hn1) hV) (mul_pos hL hV)).mpr
  nlinarith only [mul_le_mul_of_nonneg_right hlog hV.le]
end Green64Analytic.SourceBlockSieve

end

end

/-! ## SourceD23GeneralFibre -/

section

open Filter Topology
open scoped BigOperators Classical
namespace Green64Analytic.SourceBlockSieve
set_option maxHeartbeats 0
set_option autoImplicit false

noncomputable def sourceD23InclusiveCofactors (Y Δ : ℝ) (p : ℕ) : Finset ℕ :=
  (sourceD22Cell (Y/(p:ℝ)) Δ).filter (fun m => 2 ≤ m ∧ p ≤ m.minFac)

/-- No restriction on the number of prime factors is made here. -/
theorem sourceD23_general_composite_fibre (Y Δ y : ℝ) (hY : 0 ≤ Y) (n : ℕ)
    (hn : n ∈ sourceD23CompositeSet Y Δ y) :
    n.minFac ∈ sourceD23SmallPrimes Y Δ y ∧
      n/n.minFac ∈ sourceD23InclusiveCofactors Y Δ n.minFac := by
  obtain ⟨hcell,hr,hnp⟩ := Finset.mem_filter.mp hn
  have hn0 : 0 < n := by have := hr.1; omega
  have hp : n.minFac.Prime := Nat.minFac_prime (by have := hr.1; omega)
  have hquot : 2 ≤ n/n.minFac := hp.two_le.trans (Nat.minFac_le_div hn0 hnp)
  have hmul : n.minFac*(n/n.minFac)=n := Nat.mul_div_cancel' (Nat.minFac_dvd n)
  have hmin : n.minFac ≤ (n/n.minFac).minFac :=
    (source_prime_first_factor_iff_rough_cofactor n.minFac (n/n.minFac) hp hquot).mp
      (by rw [hmul])
  have hnZ : (n:ℝ) ≤ Real.exp Δ*Y :=
    (Nat.cast_le.mpr (Finset.mem_Ioc.mp hcell).2).trans
      (Nat.floor_le (mul_nonneg (Real.exp_pos _).le hY))
  have hpN := (Nat.minFac_le hn0).trans (Finset.mem_Ioc.mp hcell).2
  have hpSq : (n.minFac:ℝ)^2 ≤ n := by exact_mod_cast Nat.minFac_sq_le_self hn0 hnp
  refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),hp,hr.2,hpSq.trans hnZ⟩,?_⟩
  exact Finset.mem_filter.mpr ⟨sourceD23_divided_cell Y Δ n.minFac n hp.pos hcell
    (Nat.minFac_dvd n) hY,hquot,hmin⟩

lemma sourceD23_divided_cell_reverse (Y Δ : ℝ) (p m : ℕ) (hY : 0 ≤ Y) (hp : 0 < p)
    (hm : m ∈ sourceD22Cell (Y/(p:ℝ)) Δ) : p*m ∈ sourceD22Cell Y Δ := by
  have hpR : (0:ℝ) < p := by exact_mod_cast hp
  have hlo : Y/(p:ℝ) < (m:ℝ) :=
    (Nat.floor_lt (div_nonneg hY hpR.le)).mp (Finset.mem_Ioc.mp hm).1
  have hhi : (m:ℝ) ≤ Real.exp Δ*(Y/(p:ℝ)) :=
    (Nat.cast_le.mpr (Finset.mem_Ioc.mp hm).2).trans
      (Nat.floor_le (mul_nonneg (Real.exp_pos _).le (div_nonneg hY hpR.le)))
  apply Finset.mem_Ioc.mpr
  constructor
  · apply (Nat.floor_lt hY).mpr
    push_cast
    exact (div_lt_iff₀ hpR).mp hlo |>.trans_eq (mul_comm _ _)
  · apply Nat.le_floor
    push_cast
    have hh := mul_le_mul_of_nonneg_left hhi hpR.le
    have he : (p:ℝ)*(Real.exp Δ*(Y/(p:ℝ)))=Real.exp Δ*Y := by field_simp
    rwa [he] at hh

end Green64Analytic.SourceBlockSieve

end

/-! ## SourceD23GeneralRecurrence -/

section

open Filter Topology
open scoped BigOperators Classical
namespace Green64Analytic.SourceBlockSieve
set_option maxHeartbeats 0
set_option autoImplicit false

noncomputable def sourceD23InclusiveCount (Y Δ : ℝ) (p : ℕ) : ℝ :=
  ((sourceD23InclusiveCofactors Y Δ p).card:ℝ)

/-- Exact unrestricted Buchstab fibres for the ordinary full-cell numerator.
Repeated smallest factors remain in the inclusive p <= minFac(m) cutoff. -/
theorem sourceD23_general_composite_count (Y Δ y : ℝ) (hY : 0 ≤ Y) :
    ((sourceD23CompositeSet Y Δ y).card:ℝ) =
      ∑ p ∈ sourceD23SmallPrimes Y Δ y, sourceD23InclusiveCount Y Δ p := by
  let S := sourceD23CompositeSet Y Δ y
  let T := (sourceD23SmallPrimes Y Δ y).sigma (sourceD23InclusiveCofactors Y Δ)
  let f : ℕ → (Σ _p : ℕ, ℕ) := fun n => ⟨n.minFac,n/n.minFac⟩
  have hcard : S.card = T.card := by
    apply Finset.card_bij (fun n _ => f n)
    · intro n hn
      exact Finset.mem_sigma.mpr (sourceD23_general_composite_fibre Y Δ y hY n hn)
    · intro n hn m hm he
      have h := congrArg (fun z : (Σ _p : ℕ, ℕ) => z.1*z.2) he
      simpa only [f,Nat.mul_div_cancel' (Nat.minFac_dvd n),
        Nat.mul_div_cancel' (Nat.minFac_dvd m)] using h
    · rintro ⟨p,m⟩ hpm
      obtain ⟨hpP,hmC⟩ := Finset.mem_sigma.mp hpm
      obtain ⟨_,hp,hyp,_⟩ := Finset.mem_filter.mp hpP
      obtain ⟨hmcell,hm2,hminm⟩ := Finset.mem_filter.mp hmC
      have hmin : (p*m).minFac=p :=
        (source_prime_first_factor_iff_rough_cofactor p m hp hm2).mpr hminm
      have hpm2 : 2 ≤ p*m := by nlinarith [hp.two_le]
      have hnp : ¬(p*m).Prime := by
        intro hprime
        have hh := hprime.eq_one_or_self_of_dvd p (dvd_mul_right p m)
        rcases hh with h1 | he
        · exact hp.ne_one h1
        · nlinarith [hp.two_le]
      have hn : p*m ∈ S := Finset.mem_filter.mpr
        ⟨sourceD23_divided_cell_reverse Y Δ p m hY hp.pos hmcell,
          ⟨hpm2,by simpa only [hmin] using hyp⟩,hnp⟩
      refine ⟨p*m,hn,?_⟩
      simp only [f,hmin,Nat.mul_div_cancel_left m hp.pos]
  have hr : (S.card:ℝ) = (T.card:ℝ) := by exact_mod_cast hcard
  simpa only [T,Finset.card_sigma,Nat.cast_sum,sourceD23InclusiveCount] using hr

/-- A finite, unconditional recursion ready for all higher multiplicity strata. -/
theorem sourceD23_general_rough_upper (Y Δ y : ℝ) (hY : 0 ≤ Y) :
    sourceD22Count Y Δ y ≤ sourceD22PrimeCount Y Δ +
      ∑ p ∈ sourceD23SmallPrimes Y Δ y, sourceD23InclusiveCount Y Δ p := by
  let C := (sourceD22Cell Y Δ).filter (sourceD20Rough y)
  have hsplit := Finset.card_filter_add_card_filter_not (s:=C) (p:=Nat.Prime)
  have hsub : C.filter Nat.Prime ⊆ (sourceD22Cell Y Δ).filter Nat.Prime := by
    intro n hn
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp (Finset.mem_filter.mp hn).1).1,
      (Finset.mem_filter.mp hn).2⟩
  have he : C.filter (fun n => ¬n.Prime)=sourceD23CompositeSet Y Δ y := by
    ext n
    simp only [C,sourceD23CompositeSet,Finset.mem_filter]
    tauto
  have hc := Nat.cast_le (α:=ℝ) |>.mpr (Finset.card_le_card hsub)
  rw [he] at hsplit
  have hr : ((C.filter Nat.Prime).card:ℝ)+((sourceD23CompositeSet Y Δ y).card:ℝ)
      = sourceD22Count Y Δ y := by
    change ((C.filter Nat.Prime).card:ℝ)+((sourceD23CompositeSet Y Δ y).card:ℝ) = (C.card:ℝ)
    exact_mod_cast hsplit
  rw [sourceD23_general_composite_count Y Δ y hY] at hr
  change ((C.filter Nat.Prime).card:ℝ) ≤ sourceD22PrimeCount Y Δ at hc
  linarith


end Green64Analytic.SourceBlockSieve

end

/-! ## SourceD23RepeatedFactor -/

section

open Filter Topology
open scoped BigOperators Classical
namespace Green64Analytic.SourceBlockSieve
set_option maxHeartbeats 0
set_option autoImplicit false

noncomputable def sourceD23RepeatedCofactors (Y Δ : ℝ) (p : ℕ) : Finset ℕ :=
  (sourceD23InclusiveCofactors Y Δ p).filter (fun m => p ∣ m)

/-- Exact removal of the repeated-smallest-prime boundary. -/
theorem sourceD23_inclusive_strict_split (Y Δ : ℝ) (p : ℕ) (hp : p.Prime) :
    sourceD23InclusiveCount Y Δ p = sourceD22Count (Y/(p:ℝ)) Δ p +
      ((sourceD23RepeatedCofactors Y Δ p).card:ℝ) := by
  let C := sourceD23InclusiveCofactors Y Δ p
  have hsplit := Finset.card_filter_add_card_filter_not (s:=C) (p:=fun m => p ∣ m)
  have he : C.filter (fun m => ¬p ∣ m) =
      (sourceD22Cell (Y/(p:ℝ)) Δ).filter (sourceD20Rough p) := by
    ext m
    simp only [C,sourceD23InclusiveCofactors,sourceD20Rough,Finset.mem_filter]
    constructor
    · rintro ⟨⟨hcell,hm,hmin⟩,hnot⟩
      have hlt : p < m.minFac := lt_of_le_of_ne hmin (by
        intro heq
        exact hnot (heq ▸ Nat.minFac_dvd m))
      exact ⟨hcell,hm,by exact_mod_cast hlt⟩
    · rintro ⟨hcell,hm,hlt⟩
      have hltN : p < m.minFac := by exact_mod_cast hlt
      refine ⟨⟨hcell,hm,hltN.le⟩,?_⟩
      intro hdiv
      exact not_lt_of_ge (Nat.minFac_le_of_dvd hp.two_le hdiv) hltN
  rw [he] at hsplit
  have hh : ((sourceD23RepeatedCofactors Y Δ p).card:ℝ) +
      sourceD22Count (Y/(p:ℝ)) Δ p = sourceD23InclusiveCount Y Δ p := by
    change ((C.filter (fun m => p ∣ m)).card:ℝ) +
      (((sourceD22Cell (Y/(p:ℝ)) Δ).filter (sourceD20Rough p)).card:ℝ) = (C.card:ℝ)
    exact_mod_cast hsplit
  linarith

/-- A genuine p^2 divisor bound, independent of the rough cofactor mask. -/
theorem sourceD23_repeated_count_upper (Y Δ : ℝ) (hY : 0 ≤ Y) (p : ℕ) (hp : p.Prime) :
    ((sourceD23RepeatedCofactors Y Δ p).card:ℝ) ≤ (Real.exp Δ*Y)/(p:ℝ)^2 := by
  let Z := Real.exp Δ*Y
  let C := sourceD23RepeatedCofactors Y Δ p
  let T := Finset.Icc 1 ⌊Z/(p:ℝ)^2⌋₊
  have hpR : (0:ℝ) < p := by exact_mod_cast hp.pos
  have hmap : Set.MapsTo (fun m : ℕ => m/p) (↑C) (↑T) := by
    intro m hm
    obtain ⟨hmC,hdiv⟩ := Finset.mem_filter.mp hm
    obtain ⟨hcell,hm2,_⟩ := Finset.mem_filter.mp hmC
    have hprod : p*(m/p)=m := Nat.mul_div_cancel' hdiv
    have hmpos : 0 < m/p := by nlinarith [hp.two_le]
    have hmup : (m:ℝ) ≤ Real.exp Δ*(Y/(p:ℝ)) :=
      (Nat.cast_le.mpr (Finset.mem_Ioc.mp hcell).2).trans
        (Nat.floor_le (mul_nonneg (Real.exp_pos _).le (div_nonneg hY hpR.le)))
    have he : (p:ℝ)*((m/p:ℕ):ℝ)=m := by exact_mod_cast hprod
    have hq : ((m/p:ℕ):ℝ) ≤ Z/(p:ℝ)^2 := by
      apply (le_div_iff₀ (sq_pos_of_pos hpR)).mpr
      have hb := mul_le_mul_of_nonneg_left hmup hpR.le
      have hc : (p:ℝ)*(Real.exp Δ*(Y/(p:ℝ)))=Z := by dsimp [Z]; field_simp
      rw [hc] at hb
      nlinarith only [he,hb]
    exact Finset.mem_Icc.mpr ⟨hmpos,Nat.le_floor hq⟩
  have hinj : Set.InjOn (fun m : ℕ => m/p) (↑C) := by
    intro m hm n hn he
    have hmdiv := (Finset.mem_filter.mp hm).2
    have hndiv := (Finset.mem_filter.mp hn).2
    have h := congrArg (fun q => p*q) he
    simpa only [Nat.mul_div_cancel' hmdiv,Nat.mul_div_cancel' hndiv] using h
  have hc := Finset.card_le_card_of_injOn (fun m : ℕ => m/p) hmap hinj
  have hcast : (C.card:ℝ) ≤ (⌊Z/(p:ℝ)^2⌋₊:ℝ) := by
    simpa only [T,Nat.card_Icc,Nat.add_sub_cancel] using (Nat.cast_le (α:=ℝ)).mpr hc
  exact hcast.trans (Nat.floor_le (div_nonneg (mul_nonneg (Real.exp_pos _).le hY) (sq_nonneg _)))


end Green64Analytic.SourceBlockSieve

end

/-! ## SourceD23RepeatedTotal -/

section

open Filter Topology
open scoped BigOperators Classical
namespace Green64Analytic.SourceBlockSieve
set_option maxHeartbeats 0
set_option autoImplicit false

/-- All repeated-smallest-prime boundary terms are bounded at once. -/
theorem sourceD23_repeated_total (Y Δ y : ℝ) (hY : 0 ≤ Y) (hy : 0 ≤ y) :
    (∑ p ∈ sourceD23SmallPrimes Y Δ y, ((sourceD23RepeatedCofactors Y Δ p).card:ℝ)) ≤
      2*(Real.exp Δ*Y)/((⌊y⌋₊:ℝ)+1) := by
  let Z := Real.exp Δ*Y
  let P := sourceD23SmallPrimes Y Δ y
  let J := Finset.Ioo ⌊y⌋₊ (⌊Z⌋₊+1)
  have hsub : P ⊆ J := by
    intro p hp
    obtain ⟨hpN,hpr,hyp,_⟩ := Finset.mem_filter.mp hp
    exact Finset.mem_Ioo.mpr ⟨(Nat.floor_lt hy).mpr hyp,Finset.mem_range.mp hpN⟩
  have hs : (∑ p ∈ P, ((p:ℝ)^2)⁻¹) ≤ 2/((⌊y⌋₊:ℝ)+1) := by
    have hm := Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun p _ _ => inv_nonneg.mpr (sq_nonneg (p:ℝ)))
    exact hm.trans (sum_Ioo_inv_sq_le (α:=ℝ) ⌊y⌋₊ (⌊Z⌋₊+1))
  calc
    _ ≤ ∑ p ∈ P, Z/(p:ℝ)^2 := by
      apply Finset.sum_le_sum
      intro p hp
      exact sourceD23_repeated_count_upper Y Δ hY p (Finset.mem_filter.mp hp).2.1
    _ = Z*(∑ p ∈ P, ((p:ℝ)^2)⁻¹) := by simp only [div_eq_mul_inv,Finset.mul_sum]
    _ ≤ Z*(2/((⌊y⌋₊:ℝ)+1)) := mul_le_mul_of_nonneg_left hs (mul_nonneg (Real.exp_pos _).le hY)
    _ = _ := by ring

/-- Ordinary full-cell Buchstab recurrence with a proved, explicit repeated-factor error. -/
theorem sourceD23_strict_rough_recurrence (Y Δ y : ℝ) (hY : 0 ≤ Y) (hy : 0 ≤ y) :
    sourceD22Count Y Δ y ≤ sourceD22PrimeCount Y Δ +
      (∑ p ∈ sourceD23SmallPrimes Y Δ y, sourceD22Count (Y/(p:ℝ)) Δ p) +
      2*(Real.exp Δ*Y)/((⌊y⌋₊:ℝ)+1) := by
  have h := sourceD23_general_rough_upper Y Δ y hY
  have he : (∑ p ∈ sourceD23SmallPrimes Y Δ y, sourceD23InclusiveCount Y Δ p) =
      (∑ p ∈ sourceD23SmallPrimes Y Δ y, sourceD22Count (Y/(p:ℝ)) Δ p) +
      ∑ p ∈ sourceD23SmallPrimes Y Δ y, ((sourceD23RepeatedCofactors Y Δ p).card:ℝ) := by
    rw [←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro p hp
    exact sourceD23_inclusive_strict_split Y Δ p (Finset.mem_filter.mp hp).2.1
  rw [he] at h
  have hb := sourceD23_repeated_total Y Δ y hY hy
  linarith


end Green64Analytic.SourceBlockSieve

end

/-! ## SourceD23RepeatedSaving -/

section

open Filter Topology
open scoped BigOperators Classical
namespace Green64Analytic.SourceBlockSieve
set_option maxHeartbeats 0
set_option autoImplicit false

/-- Repeated-prime boundaries are negligible on every logarithmic cell scale. -/
theorem sourceD23_repeated_cell_saving (S γ A ε : ℝ) (hS : 0 < S) (hγ : 0 < γ) (hε : 0 < ε) :
    ∀ᶠ L : ℝ in atTop, ∀ Y : ℝ, 0 ≤ Y →
      (∑ p ∈ sourceD23SmallPrimes Y (L^(-S)) ((Real.exp L)^γ),
        ((sourceD23RepeatedCofactors Y (L^(-S)) p).card:ℝ)) ≤
      ε*((Real.exp (L^(-S))-1)*Y)/L^A := by
  have ht := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (S+A) γ hγ).const_mul (2*Real.exp 1)
  have hev : ∀ᶠ L : ℝ in atTop, 2*Real.exp 1*(L^(S+A)*Real.exp (-γ*L)) ≤ ε := by
    have h := ht.eventually_lt_const (show (2*Real.exp 1)*(0:ℝ) < ε by simpa using hε)
    filter_upwards [h] with L hL
    exact hL.le
  filter_upwards [hev,eventually_ge_atTop (1:ℝ)] with L hsmall hL1
  have hL : 0 < L := by linarith
  let Δ := L^(-S)
  let y := (Real.exp L)^γ
  have hΔ : 0 < Δ := Real.rpow_pos_of_pos hL _
  have hΔ1 : Δ ≤ 1 := by
    simpa only [Real.rpow_zero] using Real.rpow_le_rpow_of_exponent_le hL1 (show -S≤0 by linarith)
  have hy : 0 < y := Real.rpow_pos_of_pos (Real.exp_pos L) _
  have hpow : L^(S+A)*L^(-S-A)=1 := by
    rw [←Real.rpow_add hL]
    convert Real.rpow_zero L using 1
    congr 1
    ring
  have hrate : 2*Real.exp 1*Real.exp (-γ*L) ≤ ε*L^(-S-A) := by
    have h := mul_le_mul_of_nonneg_right hsmall (Real.rpow_nonneg hL.le (-S-A))
    have he : (2*Real.exp 1*(L^(S+A)*Real.exp (-γ*L)))*L^(-S-A) =
        (2*Real.exp 1*Real.exp (-γ*L))*(L^(S+A)*L^(-S-A)) := by ring
    rw [he,hpow,mul_one] at h
    exact h
  have hyinv : y⁻¹=Real.exp (-γ*L) := by
    dsimp [y]
    rw [Real.rpow_def_of_pos (Real.exp_pos L),Real.log_exp,←Real.exp_neg]
    congr 1; ring
  intro Y hY
  have hbase := sourceD23_repeated_total Y Δ y hY hy.le
  have hfloor : y ≤ (⌊y⌋₊:ℝ)+1 := (Nat.lt_floor_add_one y).le
  have hbound : 2*(Real.exp Δ*Y)/((⌊y⌋₊:ℝ)+1) ≤ (2*Real.exp 1*Real.exp (-γ*L))*Y := by
    calc
      _ ≤ 2*(Real.exp Δ*Y)/y := div_le_div_of_nonneg_left (by positivity) hy hfloor
      _ ≤ 2*(Real.exp 1*Y)/y := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hΔ1) hY)
          (by norm_num)) hy.le
      _ = _ := by rw [div_eq_mul_inv,hyinv]; ring
  have hmesh : Δ ≤ Real.exp Δ-1 := by linarith [Real.add_one_le_exp Δ]
  have halg : L^(-S-A)=Δ/L^A := by
    dsimp [Δ]
    rw [Real.rpow_sub hL]
  calc
    _ ≤ 2*(Real.exp Δ*Y)/((⌊y⌋₊:ℝ)+1) := hbase
    _ ≤ (2*Real.exp 1*Real.exp (-γ*L))*Y := hbound
    _ ≤ (ε*L^(-S-A))*Y := mul_le_mul_of_nonneg_right hrate hY
    _ = ε*(Δ*Y)/L^A := by rw [halg]; ring
    _ ≤ ε*((Real.exp Δ-1)*Y)/L^A := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hmesh hY) hε.le)
        (Real.rpow_nonneg hL.le _)

end Green64Analytic.SourceBlockSieve

end

/-! ## SourceD24SquarefreeFactorial -/

section

open Filter Topology
open scoped BigOperators Classical
namespace Green64Analytic.SourceBlockSieve
set_option maxHeartbeats 0
set_option autoImplicit false

noncomputable def sourceD24SquarefreeLengthCell
    (ell : ℕ) (Y Δ y : ℝ) : Finset ℕ :=
  (sourceD22Cell Y Δ).filter
    (fun n => sourceD20Rough y n ∧ Squarefree n ∧ n.primeFactorsList.length = ell)

noncomputable def sourceD24OrderedCellTuples
    (ell : ℕ) (Y Δ y : ℝ) : Finset (List ℕ) :=
  (Green64Analytic.OrderedPrimeRough.allPrimeTuples ell y (Real.exp Δ*Y)).filter
    (fun l => Y < (l.prod:ℝ))

lemma sourceD24_primeFactorsList_mem_ordered
    (ell : ℕ) (Y Δ y : ℝ) (hY : 0≤Y) {n : ℕ}
    (hn : n ∈ sourceD24SquarefreeLengthCell ell Y Δ y) :
    n.primeFactorsList ∈ sourceD24OrderedCellTuples ell Y Δ y := by
  obtain ⟨hcell,hr,hsq,hlen⟩ := Finset.mem_filter.mp hn
  have hn0 : 0<n := lt_of_lt_of_le Nat.zero_lt_two hr.1
  have hpr : ∀ p ∈ n.primeFactorsList, p.Prime := by
    intro p hp
    exact Nat.prime_of_mem_primeFactorsList hp
  have hbig : ∀ p ∈ n.primeFactorsList, y < (p:ℝ) := by
    intro p hp
    have hd : p∣n := (Nat.mem_primeFactorsList_iff_dvd hn0.ne' (hpr p hp)).mp hp
    exact hr.2.trans_le (Nat.cast_le.mpr
      (Nat.minFac_le_of_dvd (hpr p hp).two_le hd))
  have hprod : n.primeFactorsList.prod=n := Nat.prod_primeFactorsList hn0.ne'
  have hnupper : (n:ℝ)≤Real.exp Δ*Y :=
    (Nat.cast_le.mpr (Finset.mem_Ioc.mp hcell).2).trans
      (Nat.floor_le (mul_nonneg (Real.exp_pos _).le hY))
  have hinfo :
      n.primeFactorsList ∈
        Green64Analytic.OrderedPrimeRough.allPrimeTuples ell y (Real.exp Δ*Y) := by
    apply (Green64Analytic.OrderedPrimeRough.mem_allPrimeTuples_iff
      ell y (Real.exp Δ*Y) (mul_nonneg (Real.exp_pos _).le hY)
      n.primeFactorsList).mpr
    refine ⟨hlen,?_,?_,?_⟩
    · intro p hp
      exact ⟨hpr p hp,hbig p hp⟩
    · rw [hprod]; exact hn0
    · rw [hprod]; exact hnupper
  apply Finset.mem_filter.mpr
  refine ⟨hinfo,?_⟩
  rw [hprod]
  exact (Nat.floor_lt hY).mp (Finset.mem_Ioc.mp hcell).1

lemma sourceD24_permutations_subset
    (ell : ℕ) (Y Δ y : ℝ) (hY : 0≤Y) {n : ℕ}
    (hn : n ∈ sourceD24SquarefreeLengthCell ell Y Δ y) :
    n.primeFactorsList.permutations.toFinset ⊆
      sourceD24OrderedCellTuples ell Y Δ y := by
  intro l hl
  have hp : l.Perm n.primeFactorsList := by
    simpa only [List.mem_toFinset,List.mem_permutations] using hl
  have hbase := sourceD24_primeFactorsList_mem_ordered ell Y Δ y hY hn
  obtain ⟨hbase0,hYprod⟩ := Finset.mem_filter.mp hbase
  have hinfo := (Green64Analytic.OrderedPrimeRough.mem_allPrimeTuples_iff
    ell y (Real.exp Δ*Y) (mul_nonneg (Real.exp_pos _).le hY)
    n.primeFactorsList).mp hbase0
  apply Finset.mem_filter.mpr
  refine ⟨?_,?_⟩
  · apply (Green64Analytic.OrderedPrimeRough.mem_allPrimeTuples_iff
      ell y (Real.exp Δ*Y) (mul_nonneg (Real.exp_pos _).le hY) l).mpr
    refine ⟨hp.length_eq.trans hinfo.1,?_,?_,?_⟩
    · intro p hpl
      exact hinfo.2.1 p (hp.mem_iff.mp hpl)
    · rw [hp.prod_eq]
      exact hinfo.2.2.1
    · rw [hp.prod_eq]
      exact hinfo.2.2.2
  · rw [hp.prod_eq]
    exact hYprod

theorem sourceD24_squarefree_factorial_upper
    (ell : ℕ) (Y Δ y : ℝ) (hY : 0≤Y) :
    (ell.factorial:ℝ) *
      ((sourceD24SquarefreeLengthCell ell Y Δ y).card:ℝ) ≤
      ((sourceD24OrderedCellTuples ell Y Δ y).card:ℝ) := by
  let T := sourceD24SquarefreeLengthCell ell Y Δ y
  let S := sourceD24OrderedCellTuples ell Y Δ y
  let U := T.sigma (fun n => n.primeFactorsList.permutations.toFinset)
  let f : (Σ _n : ℕ, List ℕ) → List ℕ := fun z => z.2
  have hmap : Set.MapsTo f (↑U) (↑S) := by
    rintro ⟨n,l⟩ h
    obtain ⟨hn,hl⟩ := Finset.mem_sigma.mp h
    exact sourceD24_permutations_subset ell Y Δ y hY hn hl
  have hinj : Set.InjOn f (↑U) := by
    rintro ⟨n,l⟩ hn ⟨m,k⟩ hm he
    obtain ⟨hnT,hln⟩ := Finset.mem_sigma.mp hn
    obtain ⟨hmT,hkm⟩ := Finset.mem_sigma.mp hm
    change l = k at he
    have hpn : l.Perm n.primeFactorsList := by
      simpa only [List.mem_toFinset,List.mem_permutations] using hln
    have hpm : k.Perm m.primeFactorsList := by
      simpa only [List.mem_toFinset,List.mem_permutations] using hkm
    have hrn := (Finset.mem_filter.mp hnT).2.1
    have hrm := (Finset.mem_filter.mp hmT).2.1
    have hn0 : 0 < n := lt_of_lt_of_le Nat.zero_lt_two hrn.1
    have hm0 : 0 < m := lt_of_lt_of_le Nat.zero_lt_two hrm.1
    have hnprod : n.primeFactorsList.prod=n := Nat.prod_primeFactorsList hn0.ne'
    have hmprod : m.primeFactorsList.prod=m := Nat.prod_primeFactorsList hm0.ne'
    have hpEq : n=m := by
      have hh := congrArg List.prod he
      rw [hpn.prod_eq, hpm.prod_eq, hnprod, hmprod] at hh
      exact hh
    subst m
    subst k
    rfl
  have hc := Finset.card_le_card_of_injOn f hmap hinj
  have hcardU : U.card = T.card * ell.factorial := by
    rw [Finset.card_sigma]
    calc
      (∑ n ∈ T, n.primeFactorsList.permutations.toFinset.card)
          = ∑ _n ∈ T, ell.factorial := by
            apply Finset.sum_congr rfl
            intro n hn
            have hsq := (Finset.mem_filter.mp hn).2.2.1
            have hlen := (Finset.mem_filter.mp hn).2.2.2
            rw [List.toFinset_card_of_nodup
              (List.nodup_permutations _ hsq.nodup_primeFactorsList),
              List.length_permutations,hlen]
      _ = T.card * ell.factorial := by simp [Nat.mul_comm]
  have hc' : T.card*ell.factorial ≤ S.card := by
    rw [←hcardU]
    exact hc
  exact_mod_cast (by simpa [Nat.mul_comm] using hc')


end Green64Analytic.SourceBlockSieve

end

/-! ## SourceD24RepeatedAnyPrime -/

section

open Filter Topology
open scoped BigOperators Classical
namespace Green64Analytic.SourceBlockSieve
set_option maxHeartbeats 0
set_option autoImplicit false

noncomputable def sourceD24RepeatedCell (Y Δ y : ℝ) : Finset ℕ :=
  (sourceD22Cell Y Δ).filter (fun n => sourceD20Rough y n ∧ ¬Squarefree n)

noncomputable def sourceD24RepeatPrimes (Y Δ y : ℝ) : Finset ℕ :=
  (Finset.Ioo ⌊y⌋₊ (⌊Real.exp Δ*Y⌋₊+1)).filter Nat.Prime

noncomputable def sourceD24SquareMultipleCell (Y Δ : ℝ) (p : ℕ) : Finset ℕ :=
  (sourceD22Cell Y Δ).filter (fun n => p*p ∣ n)

lemma sourceD24_repeated_subset_union (Y Δ y : ℝ) (hY : 0≤Y) (hy : 0≤y) :
    sourceD24RepeatedCell Y Δ y ⊆
      (sourceD24RepeatPrimes Y Δ y).biUnion (sourceD24SquareMultipleCell Y Δ) := by
  have _ := hY
  intro n hn
  obtain ⟨hcell,hr,hnsq⟩ := Finset.mem_filter.mp hn
  have hn0 : 0<n := lt_of_lt_of_le Nat.zero_lt_two hr.1
  rw [Nat.squarefree_iff_prime_squarefree] at hnsq
  push Not at hnsq
  obtain ⟨p,hp,hp2⟩ := hnsq
  have hpd : p∣n := (dvd_mul_right p p).trans hp2
  have hmin : n.minFac≤p := Nat.minFac_le_of_dvd hp.two_le hpd
  have hyp : y<(p:ℝ) := hr.2.trans_le (Nat.cast_le.mpr hmin)
  have hnle : n≤⌊Real.exp Δ*Y⌋₊ := (Finset.mem_Ioc.mp hcell).2
  have hple : p≤n := Nat.le_of_dvd hn0 hpd
  have hpP : p∈sourceD24RepeatPrimes Y Δ y := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_Ioo.mpr ⟨(Nat.floor_lt hy).mpr hyp,by omega⟩,hp⟩
  apply Finset.mem_biUnion.mpr
  exact ⟨p,hpP,Finset.mem_filter.mpr ⟨hcell,hp2⟩⟩

theorem sourceD24_square_multiple_count
    (Y Δ : ℝ) (hY : 0≤Y) (p : ℕ) (hp : p.Prime) :
    ((sourceD24SquareMultipleCell Y Δ p).card:ℝ) ≤
      (Real.exp Δ*Y)/(p:ℝ)^2 := by
  let Z := Real.exp Δ*Y
  let C := sourceD24SquareMultipleCell Y Δ p
  let T := Finset.Icc 1 ⌊Z/(p:ℝ)^2⌋₊
  have hpR : (0:ℝ)<p := by exact_mod_cast hp.pos
  have hp2 : 0<p*p := Nat.mul_pos hp.pos hp.pos
  have hmap : Set.MapsTo (fun n : ℕ => n/(p*p)) (↑C) (↑T) := by
    intro n hn
    obtain ⟨hcell,hdiv⟩ := Finset.mem_filter.mp hn
    have hnpos : 0<n := by
      have hlow := (Finset.mem_Ioc.mp hcell).1
      omega
    have hqpos : 0 < n/(p*p) := by
      rw [Nat.pos_iff_ne_zero]
      intro hz
      have he := Nat.mul_div_cancel' hdiv
      rw [hz,mul_zero] at he
      omega
    have hnZ : (n:ℝ)≤Z :=
      (Nat.cast_le.mpr (Finset.mem_Ioc.mp hcell).2).trans
        (Nat.floor_le (mul_nonneg (Real.exp_pos _).le hY))
    have hq : ((n/(p*p):ℕ):ℝ)≤Z/(p:ℝ)^2 := by
      have he : (p*p)*(n/(p*p))=n := Nat.mul_div_cancel' hdiv
      have heR : ((p*p:ℕ):ℝ)*((n/(p*p):ℕ):ℝ)=n := by exact_mod_cast he
      push_cast at heR
      apply (le_div_iff₀ (sq_pos_of_pos hpR)).mpr
      nlinarith
    exact Finset.mem_Icc.mpr ⟨hqpos,Nat.le_floor hq⟩
  have hinj : Set.InjOn (fun n : ℕ => n/(p*p)) (↑C) := by
    intro n hn m hm he
    change n/(p*p)=m/(p*p) at he
    have hnD := (Finset.mem_filter.mp hn).2
    have hmD := (Finset.mem_filter.mp hm).2
    have hnE : (p*p)*(n/(p*p))=n := Nat.mul_div_cancel' hnD
    have hmE : (p*p)*(m/(p*p))=m := Nat.mul_div_cancel' hmD
    calc
      n = (p*p)*(n/(p*p)) := hnE.symm
      _ = (p*p)*(m/(p*p)) := by rw [he]
      _ = m := hmE
  have hc := Finset.card_le_card_of_injOn (fun n : ℕ => n/(p*p)) hmap hinj
  have hcardT : (T.card:ℝ)≤Z/(p:ℝ)^2 := by
    have hz : 0≤Z/(p:ℝ)^2 := div_nonneg (mul_nonneg (Real.exp_pos _).le hY) (sq_nonneg _)
    have hfloor := Nat.floor_le hz
    have hc' : T.card≤⌊Z/(p:ℝ)^2⌋₊ := by
      simp [T]
    exact (Nat.cast_le.mpr hc').trans hfloor
  exact (Nat.cast_le.mpr hc).trans hcardT

theorem sourceD24_repeated_any_prime_total
    (Y Δ y : ℝ) (hY : 0≤Y) (hy : 0≤y) :
    ((sourceD24RepeatedCell Y Δ y).card:ℝ) ≤
      2*(Real.exp Δ*Y)/((⌊y⌋₊:ℝ)+1) := by
  let P := sourceD24RepeatPrimes Y Δ y
  have hsub := sourceD24_repeated_subset_union Y Δ y hY hy
  have hcard : (sourceD24RepeatedCell Y Δ y).card ≤
      ∑ p∈P,(sourceD24SquareMultipleCell Y Δ p).card := by
    exact (Finset.card_le_card hsub).trans Finset.card_biUnion_le
  have hcast : ((sourceD24RepeatedCell Y Δ y).card:ℝ) ≤
      ∑ p∈P,((sourceD24SquareMultipleCell Y Δ p).card:ℝ) := by
    exact_mod_cast hcard
  have hpoint : ∀ p∈P, ((sourceD24SquareMultipleCell Y Δ p).card:ℝ) ≤
      (Real.exp Δ*Y)/(p:ℝ)^2 := by
    intro p hp
    exact sourceD24_square_multiple_count Y Δ hY p (Finset.mem_filter.mp hp).2
  have hsum := Finset.sum_le_sum hpoint
  have hPJ : P ⊆ Finset.Ioo ⌊y⌋₊ (⌊Real.exp Δ*Y⌋₊+1) := by
    intro p hp
    exact (Finset.mem_filter.mp hp).1
  have hsq : (∑ p∈P,((p:ℝ)^2)⁻¹) ≤ 2/((⌊y⌋₊:ℝ)+1) := by
    have h := Finset.sum_le_sum_of_subset_of_nonneg hPJ
      (fun p _ _ => inv_nonneg.mpr (sq_nonneg (p:ℝ)))
    exact h.trans (sum_Ioo_inv_sq_le (α:=ℝ) ⌊y⌋₊ (⌊Real.exp Δ*Y⌋₊+1))
  calc
    _ ≤ ∑ p∈P,((sourceD24SquareMultipleCell Y Δ p).card:ℝ) := hcast
    _ ≤ ∑ p∈P,(Real.exp Δ*Y)/(p:ℝ)^2 := hsum
    _ = (Real.exp Δ*Y)*(∑ p∈P,((p:ℝ)^2)⁻¹) := by
      simp only [div_eq_mul_inv,Finset.mul_sum]
    _ ≤ (Real.exp Δ*Y)*(2/((⌊y⌋₊:ℝ)+1)) :=
      mul_le_mul_of_nonneg_left hsq (mul_nonneg (Real.exp_pos _).le hY)
    _ = _ := by ring


end Green64Analytic.SourceBlockSieve

end

/-! ## SourceD24FiniteLengthUpper -/

section

open Filter Topology
open scoped BigOperators Classical
namespace Green64Analytic.SourceBlockSieve
set_option maxHeartbeats 0
set_option autoImplicit false

noncomputable def sourceD24SquarefreeCell (Y Δ y : ℝ) : Finset ℕ :=
  (sourceD22Cell Y Δ).filter (fun n => sourceD20Rough y n ∧ Squarefree n)

lemma sourceD24_pow_le_prod (y : ℝ) (hy : 0≤y) :
    ∀ l : List ℕ, (∀ p∈l, y≤(p:ℝ)) → y^l.length ≤ (l.prod:ℝ) := by
  intro l
  induction l with
  | nil =>
      intro h
      simp
  | cons p l ih =>
      intro h
      have hp := h p (by simp)
      have hl : ∀ q∈l,y≤(q:ℝ) := by
        intro q hq
        exact h q (by simp [hq])
      have hi := ih hl
      simp only [List.length_cons,List.prod_cons,pow_succ,Nat.cast_mul]
      calc
        y^l.length*y ≤ (l.prod:ℝ)*y := mul_le_mul_of_nonneg_right hi hy
        _ ≤ (l.prod:ℝ)*(p:ℝ) := mul_le_mul_of_nonneg_left hp (Nat.cast_nonneg _)
        _ = (p:ℝ)*(l.prod:ℝ) := by ring

lemma sourceD24_pow_lt_prod_nonempty (y : ℝ) (hy : 0≤y) (l : List ℕ)
    (hne : l≠[]) (hall : ∀ p∈l,y<(p:ℝ)) :
    y^l.length < (l.prod:ℝ) := by
  obtain ⟨p,t,rfl⟩ := List.exists_cons_of_ne_nil hne
  have hp : y<(p:ℝ) := hall p (by simp)
  have htall : ∀ q∈t,y≤(q:ℝ) := by
    intro q hq
    exact (hall q (by simp [hq])).le
  have ht := sourceD24_pow_le_prod y hy t htall
  have htpos : 0 < (t.prod:ℝ) := by
    exact_mod_cast List.prod_pos (fun q hq => by
      have hqR := hall q (by simp [hq])
      have : (0:ℝ)<q := hy.trans_lt hqR
      exact_mod_cast this)
  simp only [List.length_cons,List.prod_cons,pow_succ,Nat.cast_mul]
  calc
    y^t.length*y ≤ (t.prod:ℝ)*y :=
      mul_le_mul_of_nonneg_right ht hy
    _ < (t.prod:ℝ)*(p:ℝ) :=
      mul_lt_mul_of_pos_left hp htpos
    _ = (p:ℝ)*(t.prod:ℝ) := by ring

lemma sourceD24_squarefree_length_le
    (K : ℕ) (Y Δ y : ℝ) (hY : 0≤Y) (hy : 1≤y)
    (hcut : Real.exp Δ*Y ≤ y^(K+1)) {n : ℕ}
    (hn : n∈sourceD24SquarefreeCell Y Δ y) :
    n.primeFactorsList.length ≤ K := by
  obtain ⟨hcell,hr,hsq⟩ := Finset.mem_filter.mp hn
  by_contra hk
  have hKL : K+1≤n.primeFactorsList.length := by omega
  have hn0 : 0<n := lt_of_lt_of_le Nat.zero_lt_two hr.1
  have hlist : n.primeFactorsList≠[] := by
    intro h
    simp only [h,List.length_nil] at hKL
    omega
  have hall : ∀ p∈n.primeFactorsList,y<(p:ℝ) := by
    intro p hp
    have hpr := Nat.prime_of_mem_primeFactorsList hp
    have hd : p∣n := Nat.dvd_of_mem_primeFactorsList hp
    exact hr.2.trans_le (Nat.cast_le.mpr
      (Nat.minFac_le_of_dvd hpr.two_le hd))
  have hpown := sourceD24_pow_lt_prod_nonempty y (by linarith) n.primeFactorsList hlist hall
  have hpow : y^(K+1)≤y^n.primeFactorsList.length :=
    pow_le_pow_right₀ hy hKL
  have hprod : n.primeFactorsList.prod=n := Nat.prod_primeFactorsList hn0.ne'
  rw [hprod] at hpown
  have hnZ : (n:ℝ)≤Real.exp Δ*Y :=
    (Nat.cast_le.mpr (Finset.mem_Ioc.mp hcell).2).trans
      (Nat.floor_le (mul_nonneg (Real.exp_pos _).le hY))
  linarith

lemma sourceD24_squarefree_cell_cover
    (K : ℕ) (Y Δ y : ℝ) (hY : 0≤Y) (hy : 1≤y)
    (hcut : Real.exp Δ*Y≤y^(K+1)) :
    sourceD24SquarefreeCell Y Δ y ⊆
      (Finset.range (K+1)).biUnion
        (fun ell => sourceD24SquarefreeLengthCell ell Y Δ y) := by
  intro n hn
  have hl := sourceD24_squarefree_length_le K Y Δ y hY hy hcut hn
  apply Finset.mem_biUnion.mpr
  refine ⟨n.primeFactorsList.length,Finset.mem_range.mpr (by omega),?_⟩
  obtain ⟨hcell,hr,hsq⟩ := Finset.mem_filter.mp hn
  exact Finset.mem_filter.mpr ⟨hcell,hr,hsq,rfl⟩

theorem sourceD24_squarefree_ordered_upper
    (K : ℕ) (Y Δ y : ℝ) (hY : 0≤Y) (hy : 1≤y)
    (hcut : Real.exp Δ*Y≤y^(K+1)) :
    ((sourceD24SquarefreeCell Y Δ y).card:ℝ) ≤
      ∑ ell∈Finset.range (K+1),
        ((sourceD24OrderedCellTuples ell Y Δ y).card:ℝ)/(ell.factorial:ℝ) := by
  have hsub := sourceD24_squarefree_cell_cover K Y Δ y hY hy hcut
  have hc : (sourceD24SquarefreeCell Y Δ y).card ≤
      ∑ ell∈Finset.range (K+1),
        (sourceD24SquarefreeLengthCell ell Y Δ y).card :=
    (Finset.card_le_card hsub).trans Finset.card_biUnion_le
  have hcR : ((sourceD24SquarefreeCell Y Δ y).card:ℝ) ≤
      ∑ ell∈Finset.range (K+1),
        ((sourceD24SquarefreeLengthCell ell Y Δ y).card:ℝ) := by
    exact_mod_cast hc
  refine hcR.trans (Finset.sum_le_sum ?_)
  intro ell hell
  have hf : (0:ℝ)<(ell.factorial:ℝ) := by exact_mod_cast Nat.factorial_pos ell
  have hh := sourceD24_squarefree_factorial_upper ell Y Δ y hY
  exact (le_div_iff₀ hf).mpr (by simpa only [mul_comm] using hh)

theorem sourceD24_full_rough_ordered_upper
    (K : ℕ) (Y Δ y : ℝ) (hY : 0≤Y) (hy : 1≤y)
    (hcut : Real.exp Δ*Y≤y^(K+1)) :
    sourceD22Count Y Δ y ≤
      (∑ ell∈Finset.range (K+1),
        ((sourceD24OrderedCellTuples ell Y Δ y).card:ℝ)/(ell.factorial:ℝ)) +
      2*(Real.exp Δ*Y)/((⌊y⌋₊:ℝ)+1) := by
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
  exact add_le_add
    (sourceD24_squarefree_ordered_upper K Y Δ y hY hy hcut)
    (sourceD24_repeated_any_prime_total Y Δ y hY (by linarith))


end Green64Analytic.SourceBlockSieve

end

/-! ## SourceD24UniformFiniteUpper -/

section

open Filter Topology
open scoped BigOperators Classical
namespace Green64Analytic.SourceBlockSieve
set_option maxHeartbeats 0
set_option autoImplicit false

theorem sourceD24_exists_uniform_length_cutoff
    (S γ M : ℝ) (hS : 0<S) (hγ : 0<γ) :
    ∃ K : ℕ, ∀ᶠ L : ℝ in atTop, ∀ Y : ℝ,
      0≤Y → Y≤Real.exp (M*L) →
      Real.exp (L^(-S))*Y ≤ ((Real.exp L)^γ)^(K+1) := by
  obtain ⟨K,hK⟩ := exists_nat_gt (M/γ)
  have hgap : 0 < γ*((K+1:ℕ):ℝ)-M := by
    have hh := (div_lt_iff₀ hγ).mp hK
    push_cast
    nlinarith
  refine ⟨K,?_⟩
  filter_upwards [eventually_ge_atTop (max 1 (1/(γ*((K+1:ℕ):ℝ)-M)))]
    with L hL
  have hL1 : 1≤L := (le_max_left _ _).trans hL
  have hLp : 0<L := by linarith
  have hmesh : L^(-S)≤1 := by
    simpa only [Real.rpow_zero] using
      Real.rpow_le_rpow_of_exponent_le hL1 (show -S≤0 by linarith)
  have hbudget : 1≤(γ*((K+1:ℕ):ℝ)-M)*L := by
    have hh := (div_le_iff₀ hgap).mp ((le_max_right _ _).trans hL)
    linarith
  intro Y hY hYu
  have hleft : Real.exp (L^(-S))*Y ≤ Real.exp ((1+M*L)) := by
    calc
      _ ≤ Real.exp (L^(-S))*Real.exp (M*L) :=
        mul_le_mul_of_nonneg_left hYu (Real.exp_pos _).le
      _ = Real.exp (L^(-S)+M*L) := by rw [←Real.exp_add]
      _ ≤ Real.exp (1+M*L) := Real.exp_le_exp.mpr (by linarith)
  have hright : ((Real.exp L)^γ)^(K+1)=
      Real.exp (γ*((K+1:ℕ):ℝ)*L) := by
    rw [Real.rpow_def_of_pos (Real.exp_pos L),Real.log_exp]
    rw [←Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [hright]
  exact hleft.trans (Real.exp_le_exp.mpr (by nlinarith only [hbudget]))

theorem sourceD24_uniform_finite_rough_upper
    (S γ M : ℝ) (hS : 0<S) (hγ : 0<γ) :
    ∃ K : ℕ, ∀ᶠ L : ℝ in atTop, ∀ Y : ℝ,
      0≤Y → Y≤Real.exp (M*L) →
      sourceD22Count Y (L^(-S)) ((Real.exp L)^γ) ≤
        (∑ ell∈Finset.range (K+1),
          ((sourceD24OrderedCellTuples ell Y (L^(-S)) ((Real.exp L)^γ)).card:ℝ)/
            (ell.factorial:ℝ)) +
        2*(Real.exp (L^(-S))*Y)/((⌊(Real.exp L)^γ⌋₊:ℝ)+1) := by
  obtain ⟨K,hK⟩ := sourceD24_exists_uniform_length_cutoff S γ M hS hγ
  refine ⟨K,?_⟩
  filter_upwards [hK,eventually_ge_atTop (0:ℝ)] with L hcut hL
  intro Y hY hYu
  have hy : 1≤(Real.exp L)^γ :=
    Real.one_le_rpow (Real.one_le_exp hL) hγ.le
  exact sourceD24_full_rough_ordered_upper K Y (L^(-S)) ((Real.exp L)^γ)
    hY hy (hcut Y hY hYu)


end Green64Analytic.SourceBlockSieve

end

/-! ## SourceD24OrderedCellFubini -/

section

open Filter Topology
open scoped BigOperators Classical
namespace Green64Analytic.SourceBlockSieve
set_option maxHeartbeats 0
set_option autoImplicit false

noncomputable def sourceD24CellLastExtensions
    (pre : List ℕ) (Y Z y : ℝ) : Finset (List ℕ) :=
  (Green64Analytic.OrderedPrimeRough.primeWindow
    (max y (Y/(pre.prod:ℝ))) (Z/(pre.prod:ℝ))).image
      (fun p => pre ++ [p])

lemma sourceD24_cell_last_extensions_card
    (pre : List ℕ) (Y Z y : ℝ) :
    (sourceD24CellLastExtensions pre Y Z y).card =
      (Green64Analytic.OrderedPrimeRough.primeWindow
        (max y (Y/(pre.prod:ℝ))) (Z/(pre.prod:ℝ))).card := by
  unfold sourceD24CellLastExtensions
  apply (Finset.card_image_iff).mpr
  intro p hp q hq he
  have ht := List.append_inj_right he (rfl : pre.length=pre.length)
  simpa using ht

lemma sourceD24_cell_extensions_disjoint
    (pre₁ pre₂ : List ℕ) (Y Z y : ℝ)
    (hlen : pre₁.length=pre₂.length) (hne : pre₁≠pre₂) :
    Disjoint (sourceD24CellLastExtensions pre₁ Y Z y)
      (sourceD24CellLastExtensions pre₂ Y Z y) := by
  apply Finset.disjoint_left.mpr
  intro l h1 h2
  rcases Finset.mem_image.mp h1 with ⟨p,hp,rfl⟩
  rcases Finset.mem_image.mp h2 with ⟨q,hq,he⟩
  have hh := List.append_inj_left he.symm hlen
  exact hne hh

theorem sourceD24_ordered_cell_succ_eq_extensions
    (ell : ℕ) (Y Δ y : ℝ) (hY : 0≤Y) (hy : 0≤y) :
    sourceD24OrderedCellTuples (ell+1) Y Δ y =
      (Green64Analytic.OrderedPrimeRough.allPrimeTuples
        ell y (Real.exp Δ*Y)).biUnion
        (fun pre => sourceD24CellLastExtensions pre Y (Real.exp Δ*Y) y) := by
  ext l
  constructor
  · intro hl
    obtain ⟨hlall,hprodY⟩ := Finset.mem_filter.mp hl
    have hZ : 0≤Real.exp Δ*Y := mul_nonneg (Real.exp_pos _).le hY
    have hinfo := (Green64Analytic.OrderedPrimeRough.mem_allPrimeTuples_iff
      (ell+1) y (Real.exp Δ*Y) hZ l).mp hlall
    have hne : l≠[] := by
      intro he
      simp only [he,List.length_nil] at hinfo
      omega
    let pre := l.dropLast
    let p := l.getLast hne
    have hdec : pre++[p]=l := List.dropLast_append_getLast hne
    have hplen : pre.length=ell := by
      have hh := congrArg List.length hdec
      simp only [List.length_append,List.length_singleton] at hh
      omega
    have hprepr : ∀ q∈pre, q.Prime ∧ y<(q:ℝ) := by
      intro q hq
      apply hinfo.2.1 q
      rw [←hdec]
      exact List.mem_append_left _ hq
    have hpinfo : p.Prime ∧ y<(p:ℝ) := by
      apply hinfo.2.1 p
      rw [←hdec]
      exact List.mem_append_right _ (by simp)
    have hprepos : 0<pre.prod :=
      List.prod_pos (fun q hq => (hprepr q hq).1.pos)
    have hpreZ : (pre.prod:ℝ)≤Real.exp Δ*Y := by
      have hpone : (1:ℝ)≤p := by exact_mod_cast hpinfo.1.one_le
      have heprod : (l.prod:ℝ)=(pre.prod:ℝ)*(p:ℝ) := by
        rw [←hdec,List.prod_append,List.prod_singleton,Nat.cast_mul]
      nlinarith [hinfo.2.2.2,mul_nonneg (Nat.cast_nonneg pre.prod)
        (sub_nonneg.mpr hpone)]
    have hpre :
        pre ∈ Green64Analytic.OrderedPrimeRough.allPrimeTuples
          ell y (Real.exp Δ*Y) := by
      apply (Green64Analytic.OrderedPrimeRough.mem_allPrimeTuples_iff
        ell y (Real.exp Δ*Y) hZ pre).mpr
      exact ⟨hplen,hprepr,hprepos,hpreZ⟩
    have hpreR : (0:ℝ)<pre.prod := by exact_mod_cast hprepos
    have hupper : (p:ℝ)≤(Real.exp Δ*Y)/(pre.prod:ℝ) := by
      apply (le_div_iff₀ hpreR).mpr
      have heprod : (l.prod:ℝ)=(pre.prod:ℝ)*(p:ℝ) := by
        rw [←hdec,List.prod_append,List.prod_singleton,Nat.cast_mul]
      nlinarith [hinfo.2.2.2]
    have hlower : Y/(pre.prod:ℝ)<(p:ℝ) := by
      apply (div_lt_iff₀ hpreR).mpr
      have heprod : (l.prod:ℝ)=(pre.prod:ℝ)*(p:ℝ) := by
        rw [←hdec,List.prod_append,List.prod_singleton,Nat.cast_mul]
      nlinarith [hprodY]
    have hlow : max y (Y/(pre.prod:ℝ)) < (p:ℝ) :=
      max_lt hpinfo.2 hlower
    have hwin : p ∈ Green64Analytic.OrderedPrimeRough.primeWindow
        (max y (Y/(pre.prod:ℝ))) ((Real.exp Δ*Y)/(pre.prod:ℝ)) := by
      apply (Green64Analytic.OrderedPrimeRough.mem_primeWindow_iff_nonneg
        _ _ (le_max_of_le_left (by linarith)) (div_nonneg hZ hpreR.le) p).mpr
      exact ⟨hpinfo.1,hlow,hupper⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨pre,hpre,?_⟩
    apply Finset.mem_image.mpr
    exact ⟨p,hwin,hdec⟩
  · intro hl
    rcases Finset.mem_biUnion.mp hl with ⟨pre,hpre,hext⟩
    rcases Finset.mem_image.mp hext with ⟨p,hp,rfl⟩
    have hZ : 0≤Real.exp Δ*Y := mul_nonneg (Real.exp_pos _).le hY
    have hpreinfo := (Green64Analytic.OrderedPrimeRough.mem_allPrimeTuples_iff
      ell y (Real.exp Δ*Y) hZ pre).mp hpre
    have hpreR : (0:ℝ)<pre.prod := by exact_mod_cast hpreinfo.2.2.1
    have hpinfo := (Green64Analytic.OrderedPrimeRough.mem_primeWindow_iff_nonneg
      (max y (Y/(pre.prod:ℝ))) ((Real.exp Δ*Y)/(pre.prod:ℝ))
      (le_max_of_le_left hy)
      (div_nonneg hZ hpreR.le) p).mp hp
    apply Finset.mem_filter.mpr
    constructor
    · apply (Green64Analytic.OrderedPrimeRough.mem_allPrimeTuples_iff
        (ell+1) y (Real.exp Δ*Y) hZ (pre++[p])).mpr
      refine ⟨by simp [hpreinfo.1],?_,?_,?_⟩
      · intro q hq
        rcases (List.mem_append.mp hq) with hq|hq
        · exact hpreinfo.2.1 q hq
        · have : q=p := by simpa using hq
          subst q
          exact ⟨hpinfo.1,(le_max_left _ _).trans_lt hpinfo.2.1⟩
      · simp only [List.prod_append,List.prod_singleton]
        exact Nat.mul_pos hpreinfo.2.2.1 hpinfo.1.pos
      · simp only [List.prod_append,List.prod_singleton,Nat.cast_mul]
        simpa only [mul_comm] using (le_div_iff₀ hpreR).mp hpinfo.2.2
    · simp only [List.prod_append,List.prod_singleton,Nat.cast_mul]
      simpa only [mul_comm] using
        (div_lt_iff₀ hpreR).mp ((le_max_right _ _).trans_lt hpinfo.2.1)

theorem sourceD24_ordered_cell_succ_card_sum
    (ell : ℕ) (Y Δ y : ℝ) (hY : 0≤Y) (hy : 0≤y) :
    (sourceD24OrderedCellTuples (ell+1) Y Δ y).card =
      ∑ pre ∈ Green64Analytic.OrderedPrimeRough.allPrimeTuples
        ell y (Real.exp Δ*Y),
        (Green64Analytic.OrderedPrimeRough.primeWindow
          (max y (Y/(pre.prod:ℝ)))
          ((Real.exp Δ*Y)/(pre.prod:ℝ))).card := by
  rw [sourceD24_ordered_cell_succ_eq_extensions ell Y Δ y hY hy]
  have hdisj :
      ((Green64Analytic.OrderedPrimeRough.allPrimeTuples
        ell y (Real.exp Δ*Y) : Finset (List ℕ)) : Set (List ℕ)).PairwiseDisjoint
        (fun pre => sourceD24CellLastExtensions pre Y (Real.exp Δ*Y) y) := by
    intro pre hp q hq hne
    have hZ : 0≤Real.exp Δ*Y := mul_nonneg (Real.exp_pos _).le hY
    have hlp := ((Green64Analytic.OrderedPrimeRough.mem_allPrimeTuples_iff
      ell y (Real.exp Δ*Y) hZ pre).mp hp).1
    have hlq := ((Green64Analytic.OrderedPrimeRough.mem_allPrimeTuples_iff
      ell y (Real.exp Δ*Y) hZ q).mp hq).1
    exact sourceD24_cell_extensions_disjoint pre q Y (Real.exp Δ*Y) y
      (hlp.trans hlq.symm) hne
  rw [Finset.card_biUnion hdisj]
  apply Finset.sum_congr rfl
  intro pre hp
  exact sourceD24_cell_last_extensions_card pre Y (Real.exp Δ*Y) y


end Green64Analytic.SourceBlockSieve

end

/-! ## SourceD24LastPrimeUpper -/

section

open Filter Topology
open scoped BigOperators Classical
namespace Green64Analytic.SourceBlockSieve
set_option maxHeartbeats 0
set_option autoImplicit false

lemma sourceD24_prime_window_subset_cell
    (Y Δ y Q : ℝ) (hY : 0 ≤ Y) (hy : 0 ≤ y) (hQ : 0 < Q) :
    Green64Analytic.OrderedPrimeRough.primeWindow
      (max y (Y/Q)) ((Real.exp Δ*Y)/Q) ⊆
      (sourceD22Cell (max y (Y/Q)) Δ).filter Nat.Prime := by
  intro p hp
  have hupper0 : 0 ≤ (Real.exp Δ*Y)/Q :=
    div_nonneg (mul_nonneg (Real.exp_pos _).le hY) hQ.le
  have hlow0 : 0 ≤ max y (Y/Q) :=
    le_max_of_le_left hy
  have hinfo := (Green64Analytic.OrderedPrimeRough.mem_primeWindow_iff_nonneg
    (max y (Y/Q)) ((Real.exp Δ*Y)/Q) hlow0 hupper0 p).mp hp
  apply Finset.mem_filter.mpr
  refine ⟨?_,hinfo.1⟩
  apply Finset.mem_Ioc.mpr
  constructor
  · apply (Nat.floor_lt hlow0).mpr
    exact hinfo.2.1
  · apply Nat.le_floor
    have hbase : (max y (Y/Q):ℝ) ≥ Y/Q := le_max_right _ _
    have hup : (p:ℝ)≤Real.exp Δ*(Y/Q) := by
      calc
        (p:ℝ) ≤ (Real.exp Δ*Y)/Q := hinfo.2.2
        _ = Real.exp Δ*(Y/Q) := by field_simp
    exact hup.trans (mul_le_mul_of_nonneg_left hbase (Real.exp_pos _).le)

lemma sourceD24_prime_window_card_le_cell
    (Y Δ y Q : ℝ) (hY : 0 ≤ Y) (hy : 0 ≤ y) (hQ : 0 < Q) :
    ((Green64Analytic.OrderedPrimeRough.primeWindow
      (max y (Y/Q)) ((Real.exp Δ*Y)/Q)).card:ℝ) ≤
      sourceD22PrimeCount (max y (Y/Q)) Δ := by
  unfold sourceD22PrimeCount
  exact_mod_cast Finset.card_le_card (sourceD24_prime_window_subset_cell Y Δ y Q hY hy hQ)

lemma sourceD24_nonempty_switch_scale
    (Y Δ y Q : ℝ) (hQ : 0 < Q) (hY : 0 ≤ Y)
    (hne : (Green64Analytic.OrderedPrimeRough.primeWindow
      (max y (Y/Q)) ((Real.exp Δ*Y)/Q)).Nonempty) :
    max y (Y/Q) ≤ Real.exp Δ*(Y/Q) := by
  obtain ⟨p,hp⟩ := hne
  have hbase0 : 0 ≤ max y (Y/Q) :=
    le_max_of_le_right (div_nonneg hY hQ.le)
  have hup0 : 0 ≤ (Real.exp Δ*Y)/Q :=
    div_nonneg (mul_nonneg (Real.exp_pos _).le hY) hQ.le
  have hi := (Green64Analytic.OrderedPrimeRough.mem_primeWindow_iff_nonneg
    (max y (Y/Q)) ((Real.exp Δ*Y)/Q) hbase0 hup0 p).mp hp
  exact (hi.2.1.trans_le hi.2.2).le.trans_eq (by field_simp)

/-- Uniform PNT upper on the exact switched last-prime window. -/
theorem sourceD24_last_prime_window_upper
    (S γ ε : ℝ) (hS : 0<S) (hγ : 0<γ) (hε : 0<ε) :
    ∀ᶠ L : ℝ in atTop, ∀ Y Q : ℝ,
      0 ≤ Y → 0 < Q → ((Real.exp L)^γ) ≤ max ((Real.exp L)^γ) (Y/Q) →
      ((Green64Analytic.OrderedPrimeRough.primeWindow
        (max ((Real.exp L)^γ) (Y/Q)) ((Real.exp (L^(-S))*Y)/Q)).card:ℝ) ≤
        (1+ε)*(Real.exp (L^(-S))-1)*
          (max ((Real.exp L)^γ) (Y/Q)) /
            Real.log (max ((Real.exp L)^γ) (Y/Q)) := by
  filter_upwards [sourceD22_prime_cell_upper S γ ε hS hγ hε,
    eventually_gt_atTop (0:ℝ)] with L hpnt hL
  intro Y Q hY hQ hbase
  have hgamma : Real.exp (γ*L)=(Real.exp L)^γ := by
    rw [Real.rpow_def_of_pos (Real.exp_pos L),Real.log_exp,mul_comm]
  have hscale : Real.exp (γ*L) ≤ max ((Real.exp L)^γ) (Y/Q) := by
    rw [hgamma]
    exact hbase
  exact (sourceD24_prime_window_card_le_cell Y (L^(-S))
    ((Real.exp L)^γ) Q hY (Real.rpow_nonneg (Real.exp_pos L).le _) hQ).trans
      (hpnt _ hscale)


end Green64Analytic.SourceBlockSieve

end

/-! ## SourceD24PrefixKernelUpper -/

section

open Filter Topology
open scoped BigOperators Classical
namespace Green64Analytic.SourceBlockSieve
set_option maxHeartbeats 0
set_option autoImplicit false

noncomputable def sourceD24PrefixKernel
    (Y Δ y : ℝ) (pre : List ℕ) : ℝ :=
  if (Green64Analytic.OrderedPrimeRough.primeWindow
      (max y (Y/(pre.prod:ℝ))) ((Real.exp Δ*Y)/(pre.prod:ℝ))).Nonempty
  then ((pre.prod:ℝ)*Real.log (Y/(pre.prod:ℝ)))⁻¹
  else 0

lemma sourceD24_nonempty_prefix_scale_pos
    (Δ Y y Q : ℝ) (hΔ : Δ≤1) (hy1 : Real.exp 1<y)
    (hY : 0≤Y) (hQ : 0<Q)
    (hne : (Green64Analytic.OrderedPrimeRough.primeWindow
      (max y (Y/Q)) ((Real.exp Δ*Y)/Q)).Nonempty) :
    1 < Y/Q := by
  have hs := sourceD24_nonempty_switch_scale Y Δ y Q hQ hY hne
  have hyA : y ≤ max y (Y/Q) := le_max_left _ _
  have hEy : y ≤ Real.exp Δ*(Y/Q) := hyA.trans hs
  have hE : Real.exp Δ ≤ Real.exp 1 := Real.exp_le_exp.mpr hΔ
  have hq0 : 0 ≤ Y/Q := div_nonneg hY hQ.le
  have hbound : y ≤ Real.exp 1*(Y/Q) :=
    hEy.trans (mul_le_mul_of_nonneg_right hE hq0)
  nlinarith [Real.exp_pos 1]

lemma sourceD24_nonempty_last_window_main
    (S γ ε L Y Q : ℝ) (hS : 0<S) (hγ : 0<γ) (hε : 0<ε)
    (hL : 0<L) (hmesh : L^(-S)≤1)
    (hy1 : Real.exp 1<(Real.exp L)^γ)
    (hY : 0≤Y) (hQ : 0<Q)
    (hpnt : ∀ A : ℝ, Real.exp (γ*L)≤A →
      sourceD22PrimeCount A (L^(-S)) ≤
        (1+ε)*(Real.exp (L^(-S))-1)*A/Real.log A)
    (hne : (Green64Analytic.OrderedPrimeRough.primeWindow
      (max ((Real.exp L)^γ) (Y/Q))
      ((Real.exp (L^(-S))*Y)/Q)).Nonempty) :
    ((Green64Analytic.OrderedPrimeRough.primeWindow
      (max ((Real.exp L)^γ) (Y/Q))
      ((Real.exp (L^(-S))*Y)/Q)).card:ℝ) ≤
      (1+ε)*Real.exp (L^(-S))*(Real.exp (L^(-S))-1)*Y*
        (Q*Real.log (Y/Q))⁻¹ := by
  have _ := hS
  have _ := hγ
  let Δ := L^(-S)
  let y := (Real.exp L)^γ
  let A := max y (Y/Q)
  have hgamma : Real.exp (γ*L)=y := by
    dsimp [y]
    rw [Real.rpow_def_of_pos (Real.exp_pos L),Real.log_exp,mul_comm]
  have hscale : Real.exp (γ*L) ≤ A := by
    rw [hgamma]
    exact le_max_left _ _
  have hcard := (sourceD24_prime_window_card_le_cell Y Δ y Q hY
    (Real.rpow_nonneg (Real.exp_pos L).le _) hQ).trans (hpnt A hscale)
  have hb1 : 1<Y/Q :=
    sourceD24_nonempty_prefix_scale_pos Δ Y y Q hmesh hy1 hY hQ hne
  have hbpos : 0<Y/Q := by linarith
  have hApos : 0<A := hbpos.trans_le (le_max_right _ _)
  have hlogb : 0<Real.log (Y/Q) := Real.log_pos hb1
  have hlogA : Real.log (Y/Q) ≤ Real.log A :=
    Real.log_le_log hbpos (le_max_right _ _)
  have hAup : A ≤ Real.exp Δ*(Y/Q) :=
    sourceD24_nonempty_switch_scale Y Δ y Q hQ hY hne
  have hfrac : A/Real.log A ≤
      Real.exp Δ*(Y/Q)/Real.log (Y/Q) := by
    have hlogAp : 0<Real.log A := hlogb.trans_le hlogA
    calc
      A/Real.log A ≤ (Real.exp Δ*(Y/Q))/Real.log A :=
        div_le_div_of_nonneg_right hAup hlogAp.le
      _ ≤ (Real.exp Δ*(Y/Q))/Real.log (Y/Q) := by
        exact div_le_div_of_nonneg_left (by positivity) hlogb hlogA
  have hΔpos : 0 < Δ := by dsimp [Δ]; positivity
  have hcoef : 0 ≤ (1+ε)*(Real.exp Δ-1) := by
    exact mul_nonneg (by linarith) (sub_nonneg.mpr (Real.one_le_exp hΔpos.le))
  have hh := mul_le_mul_of_nonneg_left hfrac hcoef
  have htrans : ((Green64Analytic.OrderedPrimeRough.primeWindow
      (max y (Y/Q)) ((Real.exp Δ*Y)/Q)).card:ℝ) ≤
      (1+ε)*(Real.exp Δ-1)*(Real.exp Δ*(Y/Q)/Real.log (Y/Q)) := by
    exact hcard.trans (by simpa only [mul_div_assoc] using hh)
  dsimp [A,y,Δ] at htrans ⊢
  have heq :
      (1+ε)*(Real.exp (L^(-S))-1)*
        (Real.exp (L^(-S))*(Y/Q)/Real.log (Y/Q)) =
      (1+ε)*Real.exp (L^(-S))*(Real.exp (L^(-S))-1)*Y*
        (Q*Real.log (Y/Q))⁻¹ := by
    field_simp [hQ.ne',hlogb.ne']
  exact htrans.trans_eq heq

/-- Exact ordered-cell count is reduced to a finite prefix reciprocal kernel. -/
theorem sourceD24_ordered_cell_prefix_kernel_upper
    (ell : ℕ) (S γ ε : ℝ) (hS : 0<S) (hγ : 0<γ) (hε : 0<ε) :
    ∀ᶠ L : ℝ in atTop, ∀ Y : ℝ, 0≤Y →
      ((sourceD24OrderedCellTuples (ell+1) Y (L^(-S)) ((Real.exp L)^γ)).card:ℝ) ≤
        (1+ε)*Real.exp (L^(-S))*(Real.exp (L^(-S))-1)*Y*
          (∑ pre ∈ Green64Analytic.OrderedPrimeRough.allPrimeTuples
            ell ((Real.exp L)^γ) (Real.exp (L^(-S))*Y),
            sourceD24PrefixKernel Y (L^(-S)) ((Real.exp L)^γ) pre) := by
  filter_upwards [sourceD22_prime_cell_upper S γ ε hS hγ hε,
    eventually_ge_atTop (max 1 (2/γ))] with L hpnt hlarge
  have hL1 : 1≤L := (le_max_left _ _).trans hlarge
  have hL : 0<L := by linarith
  have hmesh : L^(-S)≤1 := by
    simpa only [Real.rpow_zero] using
      Real.rpow_le_rpow_of_exponent_le hL1 (show -S≤0 by linarith)
  have hγL : 1<γ*L := by
    have hh := (div_le_iff₀ hγ).mp ((le_max_right _ _).trans hlarge)
    linarith
  have hy1 : Real.exp 1<(Real.exp L)^γ := by
    rw [Real.rpow_def_of_pos (Real.exp_pos L),Real.log_exp,mul_comm]
    exact Real.exp_lt_exp.mpr hγL
  intro Y hY
  have hcard := sourceD24_ordered_cell_succ_card_sum ell Y (L^(-S))
    ((Real.exp L)^γ) hY (Real.rpow_nonneg (Real.exp_pos L).le _)
  rw [hcard]
  rw [Nat.cast_sum]
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro pre hpre
  have hQ : 0<(pre.prod:ℝ) := by
    have hZ : 0≤Real.exp (L^(-S))*Y :=
      mul_nonneg (Real.exp_pos _).le hY
    exact_mod_cast ((Green64Analytic.OrderedPrimeRough.mem_allPrimeTuples_iff
      ell ((Real.exp L)^γ) (Real.exp (L^(-S))*Y) hZ pre).mp hpre).2.2.1
  by_cases hne : (Green64Analytic.OrderedPrimeRough.primeWindow
      (max ((Real.exp L)^γ) (Y/(pre.prod:ℝ)))
      ((Real.exp (L^(-S))*Y)/(pre.prod:ℝ))).Nonempty
  · have hh := sourceD24_nonempty_last_window_main S γ ε L Y (pre.prod:ℝ)
      hS hγ hε hL hmesh hy1 hY hQ hpnt hne
    simpa only [sourceD24PrefixKernel,ite_eq_left hne] using hh
  · have hz : (Green64Analytic.OrderedPrimeRough.primeWindow
      (max ((Real.exp L)^γ) (Y/(pre.prod:ℝ)))
      ((Real.exp (L^(-S))*Y)/(pre.prod:ℝ))).card=0 :=
        Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp hne)
    simp only [hz,Nat.cast_zero,sourceD24PrefixKernel,ite_eq_right hne,mul_zero,le_refl]


end Green64Analytic.SourceBlockSieve

end

/-! ## SourceD24RepeatedAnySaving -/

section

open Filter Topology
open scoped BigOperators Classical
namespace Green64Analytic.SourceBlockSieve
set_option maxHeartbeats 0
set_option autoImplicit false

/-- Any repeated prime, not only a repeated smallest prime, is negligible on the full cell scale. -/
theorem sourceD24_repeated_any_cell_saving
    (S γ A ε : ℝ) (hS : 0<S) (hγ : 0<γ) (hε : 0<ε) :
    ∀ᶠ L : ℝ in atTop, ∀ Y : ℝ, 0≤Y →
      ((sourceD24RepeatedCell Y (L^(-S)) ((Real.exp L)^γ)).card:ℝ) ≤
        ε*((Real.exp (L^(-S))-1)*Y)/L^A := by
  have ht := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (S+A) γ hγ).const_mul
    (2*Real.exp 1)
  have hev : ∀ᶠ L : ℝ in atTop,
      2*Real.exp 1*(L^(S+A)*Real.exp (-γ*L)) ≤ ε := by
    have h := ht.eventually_lt_const
      (show (2*Real.exp 1)*(0:ℝ)<ε by simpa using hε)
    filter_upwards [h] with L hL
    exact hL.le
  filter_upwards [hev,eventually_ge_atTop (1:ℝ)] with L hsmall hL1
  have hL : 0<L := by linarith
  let Δ := L^(-S)
  let y := (Real.exp L)^γ
  have hΔ : 0<Δ := Real.rpow_pos_of_pos hL _
  have hΔ1 : Δ≤1 := by
    simpa only [Real.rpow_zero] using
      Real.rpow_le_rpow_of_exponent_le hL1 (show -S≤0 by linarith)
  have hy : 0<y := Real.rpow_pos_of_pos (Real.exp_pos L) _
  have hyinv : y⁻¹=Real.exp (-γ*L) := by
    dsimp [y]
    rw [Real.rpow_def_of_pos (Real.exp_pos L),Real.log_exp,←Real.exp_neg]
    congr 1
    ring
  have hpow : L^(S+A)*L^(-S-A)=1 := by
    rw [←Real.rpow_add hL]
    convert Real.rpow_zero L using 1
    congr 1
    ring
  have hrate : 2*Real.exp 1*Real.exp (-γ*L) ≤ ε*L^(-S-A) := by
    have h := mul_le_mul_of_nonneg_right hsmall (Real.rpow_nonneg hL.le (-S-A))
    have he : (2*Real.exp 1*(L^(S+A)*Real.exp (-γ*L)))*L^(-S-A) =
        (2*Real.exp 1*Real.exp (-γ*L))*(L^(S+A)*L^(-S-A)) := by ring
    rw [he,hpow,mul_one] at h
    exact h
  intro Y hY
  have hbase := sourceD24_repeated_any_prime_total Y Δ y hY hy.le
  have hfloor : y≤(⌊y⌋₊:ℝ)+1 := (Nat.lt_floor_add_one y).le
  have hbound : 2*(Real.exp Δ*Y)/((⌊y⌋₊:ℝ)+1) ≤
      (2*Real.exp 1*Real.exp (-γ*L))*Y := by
    calc
      _ ≤ 2*(Real.exp Δ*Y)/y :=
        div_le_div_of_nonneg_left (by positivity) hy hfloor
      _ ≤ 2*(Real.exp 1*Y)/y :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hΔ1) hY)
            (by norm_num)) hy.le
      _ = _ := by rw [div_eq_mul_inv,hyinv]; ring
  have hmesh : Δ≤Real.exp Δ-1 := by linarith [Real.add_one_le_exp Δ]
  have halg : L^(-S-A)=Δ/L^A := by
    dsimp [Δ]
    rw [Real.rpow_sub hL]
  calc
    _ ≤ 2*(Real.exp Δ*Y)/((⌊y⌋₊:ℝ)+1) := hbase
    _ ≤ (2*Real.exp 1*Real.exp (-γ*L))*Y := hbound
    _ ≤ (ε*L^(-S-A))*Y := mul_le_mul_of_nonneg_right hrate hY
    _ = ε*(Δ*Y)/L^A := by rw [halg]; ring
    _ ≤ ε*((Real.exp Δ-1)*Y)/L^A := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hmesh hY) hε.le)
        (Real.rpow_nonneg hL.le _)


end Green64Analytic.SourceBlockSieve

end

/-! ## SourceD26DependentLower -/

section

open Filter Topology
open scoped BigOperators Classical
namespace Green64Analytic.SourceBlockSieve
set_option maxHeartbeats 0
set_option autoImplicit false

lemma sourceD26_nonempty_window_lower_exponent
    (S γ L w Q : ℝ) (hL : 0<L) (hQ : 0<Q)
    (hne : (Green64Analytic.OrderedPrimeRough.primeWindow
      (max ((Real.exp L)^γ) (Real.exp (w*L)/Q))
      ((Real.exp (L^(-S))*Real.exp (w*L))/Q)).Nonempty) :
    γ - L^(-S-1) < w - Real.log Q/L := by
  obtain ⟨p,hp⟩ := hne
  have hy : 0 ≤ (Real.exp L)^γ := Real.rpow_nonneg (Real.exp_pos L).le _
  have hY : 0 ≤ Real.exp (w*L) := (Real.exp_pos _).le
  have hup0 : 0 ≤ (Real.exp (L^(-S))*Real.exp (w*L))/Q :=
    div_nonneg (mul_nonneg (Real.exp_pos _).le hY) hQ.le
  have hlo0 : 0 ≤ max ((Real.exp L)^γ) (Real.exp (w*L)/Q) :=
    le_max_of_le_left hy
  have hi := (Green64Analytic.OrderedPrimeRough.mem_primeWindow_iff_nonneg
    _ _ hlo0 hup0 p).mp hp
  have hpy : (Real.exp L)^γ < (p:ℝ) :=
    (le_max_left _ _).trans_lt hi.2.1
  have hpup : (p:ℝ) ≤ (Real.exp (L^(-S))*Real.exp (w*L))/Q := hi.2.2
  have hp0 : 0<(p:ℝ) := by exact_mod_cast hi.1.pos
  have hy0 : 0<(Real.exp L)^γ := Real.rpow_pos_of_pos (Real.exp_pos L) _
  have hloglo := Real.log_lt_log hy0 hpy
  have hlogup := Real.log_le_log hp0 hpup
  have hleft : Real.log ((Real.exp L)^γ)=γ*L := by
    rw [Real.rpow_def_of_pos (Real.exp_pos L),Real.log_exp,Real.log_exp]
    ring
  have hright :
      Real.log ((Real.exp (L^(-S))*Real.exp (w*L))/Q) =
        L^(-S)+w*L-Real.log Q := by
    rw [Real.log_div (mul_pos (Real.exp_pos _) (Real.exp_pos _)).ne' hQ.ne',
      Real.log_mul (Real.exp_pos _).ne' (Real.exp_pos _).ne',
      Real.log_exp,Real.log_exp]
  rw [hleft] at hloglo
  rw [hright] at hlogup
  have hcore : γ*L < L^(-S)+w*L-Real.log Q := hloglo.trans_le hlogup
  have hpow : L^(-S)/L = L^(-S-1) := by
    have hh := Real.rpow_sub hL (-S) 1
    rw [Real.rpow_one] at hh
    simpa only [show -S-1 = (-S)-1 by ring] using hh.symm
  have hh0 : γ < (L^(-S)+w*L-Real.log Q)/L :=
    (lt_div_iff₀ hL).mpr hcore
  have heq : (L^(-S)+w*L-Real.log Q)/L =
      L^(-S)/L + w - Real.log Q/L := by
    field_simp [hL.ne']
  rw [heq] at hh0
  have hh := hh0
  rw [hpow] at hh
  linarith


end Green64Analytic.SourceBlockSieve

end

/-! ## SourceTwoThresholdArcs -/

section

namespace Green64Analytic.CorrelationD

/-- Source-correct two thresholds:
D=H'/Q is the Dirichlet-approximation scale whereas S is
the independent small/large denominator cutoff.
In the small branch q<|k|S, but the arc width is 2D/H'. -/
theorem source_dirichlet_two_threshold_arcs
    (k : ℤ) (theta Hprime D S : ℝ)
    (hk : k ≠ 0) (hD : 0 < D)
    (hHR : 2*D ≤ Hprime) :
    ∃ (a : ℤ) (r : ℕ),
      0 < r ∧ r ≤ ⌊Hprime/D⌋₊ ∧
      Int.gcd a (r:ℤ) = 1 ∧
      |(k:ℝ)*theta - (a:ℝ)/(r:ℝ)| ≤ 1/((r:ℝ)^2) ∧
      (S ≤ (r:ℝ) ∨
        ∃ (h0 z : ℤ) (q : ℕ),
          (r:ℝ) < S ∧ q = k.natAbs*r ∧ 0 < q ∧
          (q:ℝ) < (k.natAbs:ℝ)*S ∧
          0 ≤ h0 ∧ h0 < (q:ℤ) ∧
          |theta-(z:ℝ)-(h0:ℝ)/(q:ℝ)| ≤ 2*D/Hprime) := by
  obtain ⟨a,r,q,h0,z,hr,hrCap,hcop,hC6,
      hq,hqpos,hqCap,hh0,hh0lt,hArc⟩ :=
    source_circle_dirichlet_lift k theta Hprime D hk hD hHR
  refine ⟨a,r,hr,hrCap,hcop,hC6,?_⟩
  rcases le_or_gt S (r:ℝ) with hlarge | hsmall
  · exact Or.inl hlarge
  · right
    have hkNat : (0:ℝ) < (k.natAbs:ℝ) := by
      exact_mod_cast ((Int.natAbs_pos).mpr hk)
    have hqCast : (q:ℝ) = (k.natAbs:ℝ)*(r:ℝ) := by
      rw [hq]
      simp only [Nat.cast_mul]
    have hqSmall : (q:ℝ) < (k.natAbs:ℝ)*S := by
      rw [hqCast]
      exact mul_lt_mul_of_pos_left hsmall hkNat
    exact ⟨h0,z,q,hsmall,hq,hqpos,hqSmall,hh0,hh0lt,hArc⟩
end Green64Analytic.CorrelationD

end

/-! ## SourceFloorScaleEventually -/

section

open Filter Real

namespace Green64Analytic.CorrelationD

/-- Source lower comparison cell scales imply an actual nonempty
Dirichlet search Q=floor(H'/L^Cprime), with H'=U1*U2.
The exponent Cprime may be fixed arbitrarily large. -/
theorem eventually_source_floor_dirichlet_nonempty
    (c Cprime C₁ C₂ : ℝ) (hc : 0 < c) :
    ∀ᶠ L : ℝ in atTop,
      2 ≤ L ∧
      ∀ (U1 U2 Hprime : ℝ),
        Real.exp (L^c-C₁) ≤ U1 →
        Real.exp (L^c-C₂) ≤ U2 →
        Hprime = U1*U2 →
        2*L^Cprime ≤ Hprime := by
  have hLo1 := eventually_source_comparison_lower c (Cprime+1) C₁ hc
  have hLo2 := eventually_source_comparison_lower c 0 C₂ hc
  filter_upwards [hLo1,hLo2,eventually_ge_atTop (2:ℝ)]
    with L h1 h2 hL
  refine ⟨hL,?_⟩
  intro U1 U2 Hprime hu1 hu2 hH
  have hLp : 0 < L := by linarith
  have hp : 0 ≤ L^Cprime := (Real.rpow_pos_of_pos hLp Cprime).le
  have hpow : L^(Cprime+1) = L^Cprime*L := by
    rw [Real.rpow_add hLp]
    simp only [Real.rpow_one]
  have hU1 : L^(Cprime+1) ≤ U1 := (le_of_lt h1).trans hu1
  have hU2 : (1:ℝ) ≤ U2 := by
    have hh : (1:ℝ) < Real.exp (L^c-C₂) := by
      simpa only [Real.rpow_zero] using h2
    exact (le_of_lt hh).trans hu2
  have hPowBound : 2*L^Cprime ≤ L^(Cprime+1) := by
    rw [hpow]
    calc
      2*L^Cprime = L^Cprime*2 := by ring
      _ ≤ L^Cprime*L := mul_le_mul_of_nonneg_left hL hp
  have hHmul : U1 ≤ U1*U2 := by
    have hu1pos : 0 ≤ U1 := by
      exact le_trans (Real.exp_pos _).le hu1
    calc
      U1 = U1*1 := by ring
      _ ≤ U1*U2 := mul_le_mul_of_nonneg_left hU2 hu1pos
  rw [hH]
  exact (hPowBound.trans hU1).trans hHmul
end Green64Analytic.CorrelationD

end

/-! ## SourceMajorArcScale -/

section

open Filter Real

/-- The exact source choice H=H'/L^Carc eventually satisfies
H≥2 from the original stretched-exponential comparison scales.
No extra local Fourier window hypothesis is needed asymptotically. -/
theorem source_major_arc_window_at_least_two
    (L Hprime Carc : ℝ) (hLp : 0 < L)
    (hHprime : 2*L^Carc ≤ Hprime) :
    2 ≤ Hprime/L^Carc := by
  have hpow : 0 < L^Carc := Real.rpow_pos_of_pos hLp Carc
  exact (le_div_iff₀ hpow).mpr hHprime

theorem eventually_source_major_arc_window_at_least_two
    (c Carc C₁ C₂ : ℝ) (hc : 0 < c) :
    ∀ᶠ L : ℝ in atTop,
      2 ≤ L ∧
      ∀ (U1 U2 Hprime : ℝ),
        Real.exp (L^c-C₁) ≤ U1 →
        Real.exp (L^c-C₂) ≤ U2 →
        Hprime = U1*U2 →
        2 ≤ Hprime/L^Carc := by
  have hFloor :=
    Green64Analytic.CorrelationD.eventually_source_floor_dirichlet_nonempty
      c Carc C₁ C₂ hc
  filter_upwards [hFloor] with L hsource
  obtain ⟨hL,hbound⟩ := hsource
  refine ⟨hL,?_⟩
  intro U1 U2 Hprime hU1 hU2 hH
  exact source_major_arc_window_at_least_two
    L Hprime Carc (by linarith)
    (hbound U1 U2 Hprime hU1 hU2 hH)

end

/-! ## SourceU1IntervalEnergy -/

section

open MeasureTheory
open scoped BigOperators
namespace Green64Analytic.LongPrime

/-- Genuine long-prime polynomial is continuous in real Mellin time,
including the fixed shifted frequency. -/
theorem source_long_prime_shifted_continuous
    (q : ℕ) (χ : DirichletCharacter ℂ q) (N : ℝ)
    (I : Set ℝ) (σ : ℝ) :
    Continuous (fun t : ℝ =>
      sourceCorrelationLongPrime q χ N I (t+σ)) := by
  classical
  unfold sourceCorrelationLongPrime
  apply continuous_finset_sum
  intro p hp
  have hpPrime : Nat.Prime p := by
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2
  have hpNe : (p:ℂ) ≠ 0 := by
    exact_mod_cast hpPrime.ne_zero
  have hExp : Continuous (fun t : ℝ =>
      (-1:ℂ) + ((t+σ:ℝ):ℂ)*Complex.I) := by fun_prop
  have hPow := hExp.const_cpow (Or.inl hpNe)
  exact continuous_const.mul hPow

/-- Genuine shifted U1 controls the complete exceptional-interval
high-frequency mean square without any loss in interval count. -/
theorem source_shifted_U1_high_frequency_interval_energy
    (τ η C A : ℝ)
    (hτ : 0 < τ) (hτη : τ < η) (hη : η < 1/4)
    (hC : 0 < C) (hA : 0 < A) :
    ∃ B₀ K X₀ : ℝ, 0 < B₀ ∧ 0 < K ∧ 3 ≤ X₀ ∧
    ∀ x : ℝ, X₀ ≤ x →
    ∀ N : ℝ, x^τ/2 ≤ N → N ≤ x^η →
    ∀ q : ℕ, 1 ≤ q → (q:ℝ) ≤ (Real.log x)^C →
    ∀ χ : DirichletCharacter ℂ q,
    ∀ I : Set ℝ, Set.OrdConnected I →
      I ⊆ Set.Icc N (2*N) →
    ∀ (σ : ℝ) (J : Finset ℤ) (F : ℝ → ℂ),
      Continuous F →
      (∀ j ∈ J, ∀ t ∈ Set.Icc (j:ℝ) ((j:ℝ)+1),
         (Real.log x)^B₀+|σ| ≤ |t|) →

      (∀ j ∈ J, ∀ t ∈ Set.Icc (j:ℝ) ((j:ℝ)+1),
         |t+σ| ≤ x^2) →
      ∀ (R : ℝ),
      (∑ j ∈ J,
        ∫ t in Set.Icc (j:ℝ) ((j:ℝ)+1), ‖F t‖^2) ≤ R →
      (∑ j ∈ J,
        ∫ t in Set.Icc (j:ℝ) ((j:ℝ)+1),
          ‖sourceCorrelationLongPrime q χ N I (t+σ) * F t‖^2) ≤
      (K/(Real.log x)^A)^2 * R := by
  obtain ⟨B₀,K,X₀,hB₀,hK,hX₀,hBound⟩ :=
    sourceCorrelationLongPrime_shifted_U1 τ η C A
      hτ hτη hη hC hA
  refine ⟨B₀,K,X₀,hB₀,hK,hX₀,?_⟩
  intro x hx N hNl hNu q hq hqC χ I hI hSub
    σ J F hF hLow hHigh R hR
  let δ : ℝ := K/(Real.log x)^A
  have hx3 : 3 ≤ x := hX₀.trans hx
  have hlogx : 0 < Real.log x := Real.log_pos (by linarith)
  have hδ : 0 ≤ δ := by
    dsimp [δ]
    positivity
  let G : ℝ → ℂ := fun t =>
    sourceCorrelationLongPrime q χ N I (t+σ)
  have hG : Continuous G :=
    source_long_prime_shifted_continuous q χ N I σ
  have hGt : ∀ j ∈ J, ∀ t ∈ Set.Icc (j:ℝ) ((j:ℝ)+1),
      ‖G t‖ ≤ δ := by
    intro j hj t ht
    exact hBound x hx N hNl hNu q hq hqC χ I hI hSub
      t σ (hLow j hj t ht) (hHigh j hj t ht)
  have hUnit (j : ℤ) (hj : j ∈ J) :
      (∫ t in Set.Icc (j:ℝ) ((j:ℝ)+1), ‖G t * F t‖^2) ≤
      δ^2 * (∫ t in Set.Icc (j:ℝ) ((j:ℝ)+1), ‖F t‖^2) := by
    let S : Set ℝ := Set.Icc (j:ℝ) ((j:ℝ)+1)
    have hInt : IntegrableOn (fun t : ℝ => ‖G t * F t‖^2) S :=
      ((hG.mul hF).norm.pow 2).continuousOn.integrableOn_compact
        isCompact_Icc

    have hFInt : IntegrableOn (fun t : ℝ => ‖F t‖^2) S :=
      (hF.norm.pow 2).continuousOn.integrableOn_compact isCompact_Icc
    have hBInt : IntegrableOn (fun t : ℝ => δ^2 * ‖F t‖^2) S :=
      hFInt.const_mul _
    have hPoint (t : ℝ) (ht : t ∈ S) :
        ‖G t * F t‖^2 ≤ δ^2 * ‖F t‖^2 := by
      have hb := hGt j hj t ht
      have hsq : ‖G t‖^2 ≤ δ^2 := by
        nlinarith [norm_nonneg (G t)]
      calc
        _ = ‖G t‖^2 * ‖F t‖^2 := by rw [norm_mul]; ring
        _ ≤ δ^2 * ‖F t‖^2 :=
          mul_le_mul_of_nonneg_right hsq (sq_nonneg _)
    calc
      _ ≤ (∫ t in S, δ^2 * ‖F t‖^2) :=
        setIntegral_mono_on hInt hBInt measurableSet_Icc hPoint
      _ = δ^2 * (∫ t in S, ‖F t‖^2) := by
        rw [integral_const_mul]
  change (∑ j ∈ J,
      ∫ t in Set.Icc (j:ℝ) ((j:ℝ)+1),
        ‖G t * F t‖^2) ≤ δ^2 * R
  calc
    _ ≤ ∑ j ∈ J, δ^2 *
        (∫ t in Set.Icc (j:ℝ) ((j:ℝ)+1), ‖F t‖^2) := by
      apply Finset.sum_le_sum
      intro j hj
      exact hUnit j hj
    _ = δ^2 * ∑ j ∈ J,
        (∫ t in Set.Icc (j:ℝ) ((j:ℝ)+1), ‖F t‖^2) := by
      rw [Finset.mul_sum]
    _ ≤ δ^2 * R :=
      mul_le_mul_of_nonneg_left hR (sq_nonneg δ)
end Green64Analytic.LongPrime

end

