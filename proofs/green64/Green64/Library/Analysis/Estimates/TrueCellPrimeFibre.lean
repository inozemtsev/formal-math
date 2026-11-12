module

public import Green64.Library.Weights.Part097
public import Green64.Library.Weights.NonemptyQSkipCoarseChart
public import Green64.Library.Analysis.Estimates.ConditionalPrimeFibre

@[expose] public section

/-!
# Analysis / Estimates / TrueCellPrimeFibre

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## OriginalTrueCellPrimeFibre -/

section

open scoped BigOperators Classical
open Filter
noncomputable section

/-! Native extraction of the original D31/D36 definitions below. Their
bodies and original names are unchanged; the source files and their
SHA256 digests are preserved in inputs/B572_source_provenance. These
were absent from the previous Lean 4.34.1 import closure. -/
namespace Green64Analytic.SourceBlockSieve

noncomputable def shiftTwoOriginalGroupFactor (P : Finset ℕ) (u : ℕ) : ℝ :=
  (shiftTwoGroupOmega P u : ℝ) *
    (1/2:ℝ)^(shiftTwoGroupOmega P u - 1) /
    (∑ p ∈ P, (p:ℝ)⁻¹)

noncomputable def sourceOriginalOrdinaryCoefficient
    {B : Type} [Fintype B] [DecidableEq B]
    (r : ℕ) (Q : B → Finset ℕ) (v : ℕ) : ℝ :=
  if ∃ f : (b : B) → (Fin r → {p // p ∈ Q b}),
       (∏ b : B, ∏ i : Fin r, (f b i).val) = v
  then ∏ b : B, ∏ p ∈ Q b, (((v.factorization p).factorial:ℝ)⁻¹)
  else 0

noncomputable def sourceOriginalW1
    {G : Type} [Fintype G] (P : G → Finset ℕ) (u : ℕ) : ℝ :=
  ∏ g : G, shiftTwoOriginalGroupFactor (P g) u

noncomputable def sourceOriginalA0
    {B G : Type} [Fintype B] [DecidableEq B] [Fintype G]
    (r : ℕ) (Q : B → Finset ℕ) (P : G → Finset ℕ)
    (u : ℕ) : ℝ :=
  sourceOriginalW1 P u *
    sourceOriginalOrdinaryCoefficient r Q
      (sourceOriginalOrdinaryPart (Finset.univ.biUnion P) u)

noncomputable def sourceOriginalA
    {B G : Type} [Fintype B] [DecidableEq B] [Fintype G]
    (r : ℕ) (Q : B → Finset ℕ) (P : G → Finset ℕ)
    (u : ℕ) : ℝ :=
  sourceOriginalA0 r Q P u *
    ((1 - (-1:ℝ)^sourceOriginalPParityExponent
       (Finset.univ.biUnion P) u)/2)

-- The imported original weight primitives remain literally the originals.
example (P : Finset ℕ) (u : ℕ) :
    shiftTwoGroupOmega P u = (P.filter (fun p => p ∣ u)).card := rfl
example (Pall : Finset ℕ) (u : ℕ) :
    sourceOriginalOrdinaryPart Pall u = ∏ p ∈ u.primeFactors \ Pall, p ^ u.factorization p := rfl
example (Pall : Finset ℕ) (u : ℕ) :
    sourceOriginalPParityExponent Pall u = ∑ p ∈ Pall, u.factorization p := rfl

end Green64Analytic.SourceBlockSieve

namespace Green64Analytic.ShiftTwoTerminal
open SourceBlockSieve

noncomputable def originalWeight (r₀ : ℕ) (x : ℝ) (u : ℕ) : ℝ :=
  let d := sourceOriginalLiteralDepth r₀ (Real.log x)
  sourceOriginalA r₀ (sourceOriginalQActualBands r₀ d (Real.log x))
    (sourceOriginalPAllActualBands r₀ (Real.log x)) u

noncomputable def typeIISum (r₀ : ℕ) (Ψ : ℝ → ℝ) (x : ℝ)
    (K J : Finset ℕ) (α β : ℕ → ℂ) : ℂ :=
  ∑ m ∈ K, ∑ n ∈ J, if 3 ≤ m*n then
    α m * β n * (originalWeight r₀ x (m*n-2) *
      Ψ (((m*n-2 : ℕ) : ℝ)/x) : ℝ) else 0

end Green64Analytic.ShiftTwoTerminal

namespace Green64Analytic.SourceBlockSieve
open Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
noncomputable def sourceD31PrimeGrid (b c : ℝ) (N i : ℕ) : ℝ :=
  b + (c-b)*(i:ℝ)/(N:ℝ)

noncomputable def sourceD31PrimeFloor (b c : ℝ) (N : ℕ)
    (L : ℝ) (i : ℕ) : ℕ :=
  ⌊Real.exp (sourceD31PrimeGrid b c N i*L)⌋₊

noncomputable def sourceD31PrimeBin (b c : ℝ) (N : ℕ)
    (L : ℝ) (i : ℕ) : Finset ℕ :=
  (Finset.Ioc (sourceD31PrimeFloor b c N L i)
    (sourceD31PrimeFloor b c N L (i+1))).filter Nat.Prime

noncomputable def sourceD36OriginalTrueCell
    (r₀ : ℕ) (Ψ : ℝ → ℝ) (σ b c : ℝ)
    (N i j k : ℕ) (L : ℝ) : ℂ :=
  let a := sourceD31PrimeGrid b c N i
  let η := sourceD31PrimeGrid b c N (i+1)
  let f : ℕ → ℝ := sourceD20FullDelta (L^(-σ))
    (Real.exp (Real.sqrt L)) ((Real.exp L)^a)
  typeIISum r₀ Ψ (Real.exp L)
    (sourceD36DyadicInterval j)
    (sourceD36DyadicInterval k)
    (fun m => if m≤⌊2*Real.exp L⌋₊+2 then
      sourceD36OriginalCofactorMask a η (b/4) L f m else 0)
    (fun p => if p≤⌊Real.exp (η*L)⌋₊ ∧
      p∈sourceD31PrimeBin b c N L i then (1:ℂ) else 0)

end Green64Analytic.SourceBlockSieve
namespace Green64Analytic.ShiftTwoTerminal
open Green64Analytic.SourceBlockSieve Green64ComparisonPartial
set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 10000

/-- The TRUE second-coordinate dyad intersected with the original sparse
prime bin. No primality indicator or product condition is dropped. -/
def sourceNativeB572TrueBetaSet434
    (b c L : ℝ) (N i k : ℕ) : Finset ℕ :=
  (sourceD36DyadicInterval k).filter (fun n => n ∈ sourceD31PrimeBin b c N L i)

/-- The unsplit original cell, written on its exact sparse beta support.
This is a source-identification theorem, not an estimate or nonvanishing
claim. The same arbitrary original witness Psi and full sigma=1 Delta
are retained, with every physical cofactor mask and cutoff. -/
theorem source_native_B572_original_true_cell_sparse_beta434
    (r : ℕ) (Ψ : ℝ → ℝ) (b c L : ℝ) (N i j k : ℕ) :
    sourceD36OriginalTrueCell r Ψ 1 b c N i j k L =
      ∑ m ∈ sourceD36DyadicInterval j,
        ∑ n ∈ sourceNativeB572TrueBetaSet434 b c L N i k,
          if 3 ≤ m*n then
            sourceNativeB563OriginalD61Alpha434
              (sourceD31PrimeGrid b c N i) (sourceD31PrimeGrid b c N (i+1)) b L m *
              (originalWeight r (Real.exp L) (m*n-2) *
                Ψ (((m*n-2:ℕ):ℝ)/Real.exp L):ℝ) else 0 := by
  unfold sourceD36OriginalTrueCell typeIISum
  apply Finset.sum_congr rfl
  intro m hm
  rw [sourceNativeB572TrueBetaSet434,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hbin : n ∈ sourceD31PrimeBin b c N L i
  · have hupper : n ≤ ⌊Real.exp (sourceD31PrimeGrid b c N (i+1)*L)⌋₊ :=
      (Finset.mem_Ioc.mp (Finset.mem_filter.mp hbin).1).2
    simp only [hbin,hupper,and_self,ite_true,mul_one]
    rfl
  · simp only [hbin,and_false,ite_false,mul_zero,zero_mul,ite_self]

private theorem B572_grid_mem
    (b c : ℝ) (N i : ℕ) (hbc : b<c) (hN : 0<N) (hi : i≤N) :
    b ≤ sourceD31PrimeGrid b c N i ∧ sourceD31PrimeGrid b c N i ≤ c := by
  have hNr : (0:ℝ)<N := by exact_mod_cast hN
  have hIr : (0:ℝ)≤(i:ℝ) := Nat.cast_nonneg _
  have hINr : (i:ℝ)≤N := by exact_mod_cast hi
  have hD : 0≤ c-b := sub_nonneg.mpr hbc.le
  have hlow : 0≤(c-b)*(i:ℝ)/(N:ℝ) :=
    div_nonneg (mul_nonneg hD hIr) hNr.le
  have hupp : (c-b)*(i:ℝ)/(N:ℝ)≤ c-b := by
    apply (div_le_iff₀ hNr).mpr
    nlinarith [mul_le_mul_of_nonneg_left hINr hD]
  dsimp [sourceD31PrimeGrid]
  constructor <;> linarith

private theorem B572_active_support
    (a eta b L : ℝ) (j m : ℕ)
    (hWy : Real.exp (Real.sqrt L) ≤ (Real.exp L)^a)
    (hm : m ∈ sourceNativeB563OriginalD61ActiveK434 a eta b L j) :
    rough (Real.exp (Real.sqrt L)) m ∧ Real.exp ((1-eta)*L) ≤ (m:ℝ) := by
  have hmB := (Finset.mem_Icc.mp (Finset.mem_filter.mp hm).1).1
  have hmpos : 0 < m := (by positivity : 0<(2:ℕ)^j).trans_le hmB
  have hAlpha := (Finset.mem_filter.mp hm).2
  have hDelta : sourceD20FullDelta (L^(-(1:ℝ)))
      (Real.exp (Real.sqrt L)) ((Real.exp L)^a) m ≠ 0 := by
    intro hz
    apply hAlpha
    simp [sourceNativeB563OriginalD61Alpha434,sourceD36OriginalCofactorMask,hz]
  refine ⟨⟨hmpos,original_D20_full_delta_support_SourceRoughAbove434
    (L^(-(1:ℝ))) (Real.exp (Real.sqrt L)) ((Real.exp L)^a) m hWy hDelta⟩,?_⟩
  unfold sourceNativeB563OriginalD61Alpha434 at hAlpha
  split_ifs at hAlpha with hclip
  · unfold sourceD36OriginalCofactorMask at hAlpha
    split_ifs at hAlpha with hmask
    · exact hmask.1
    · exact False.elim (hAlpha rfl)
  · exact False.elim (hAlpha rfl)

private theorem B572_Q0_lt_active
    (d j m p : ℕ) (a eta b L : ℝ) (hL : 1≤L) (heta : eta≤1/2)
    (hWy : Real.exp (Real.sqrt L) ≤ (Real.exp L)^a)
    (hm : m ∈ sourceNativeB563OriginalD61ActiveK434 a eta b L j)
    (hp : p ∈ sourceOriginalQActualBands 6 d L ⟨0,by omega⟩) : p < m := by
  have hpUpper : (p:ℝ) ≤ Real.exp ((1/11:ℝ)*L) := by
    have h := (Nat.le_floor_iff (Real.exp_nonneg _)).mp
      (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).2
    convert h using 1
    norm_num [sourceOriginalQActualExponent,sourceOriginalQ0Scale]
  have hmLower := (B572_active_support a eta b L j m hWy hm).2
  have hExp : Real.exp ((1/11:ℝ)*L) < Real.exp ((1-eta)*L) := by
    apply Real.exp_lt_exp.mpr
    have hLp : 0<L := by linarith
    exact mul_lt_mul_of_pos_right (by linarith : (1/11:ℝ)<1-eta) hLp
  exact_mod_cast hpUpper.trans_lt (hExp.trans_le hmLower)

private theorem B572_rough_scale_two (L : ℝ) (hL : 1≤L) :
    (2:ℝ) ≤ Real.exp (Real.sqrt L) := by
  have hs : (1:ℝ) ≤ Real.sqrt L := by
    simpa using Real.sqrt_le_sqrt hL
  have he : (2:ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1:ℝ)]
  exact he.trans (Real.exp_le_exp.mpr hs)

private theorem B572_shift_two_coprime
    (W : ℝ) (m B p n : ℕ) (hm : rough W m) (hW : 2≤W)
    (he : B*p+2=m*n) : Nat.Coprime m B := by
  apply source_native_B547_smooth_comparison_shift_coprime434 W m B (m*n) 1 (-1)
    hm (by norm_num) (by simpa using hW)
  · intro q hq hd
    have := Nat.dvd_one.mp hd
    exact False.elim (hq.ne_one this)
  · exact dvd_mul_right m n
  · refine ⟨(p:ℤ),?_⟩
    have heI : ((B*p+2:ℕ):ℤ)=((m*n:ℕ):ℤ) := congrArg Nat.cast he
    push_cast at heI ⊢
    linarith

private theorem B572_prime_unique
    (m B p1 p2 n1 n2 : ℕ) (hm : 0 < m) (hc : Nat.Coprime m B)
    (hp1 : p1 < m) (hp2 : p2 < m)
    (he1 : B*p1+2=m*n1) (he2 : B*p2+2=m*n2) : p1=p2 ∧ n1=n2 := by
  have hstep (p q u v : ℕ) (hpq : p≤q) (hq : q < m)
      (hep : B*p+2=m*u) (heq : B*q+2=m*v) : p=q := by
    have hdivI : (m:ℤ) ∣ (B:ℤ)*((q:ℤ)-(p:ℤ)) := by
      refine ⟨(v:ℤ)-(u:ℤ),?_⟩
      have hepi : ((B*p+2:ℕ):ℤ)=((m*u:ℕ):ℤ) := congrArg Nat.cast hep
      have heqi : ((B*q+2:ℕ):ℤ)=((m*v:ℕ):ℤ) := congrArg Nat.cast heq
      push_cast at hepi heqi
      nlinarith
    have hdiv : m ∣ B*(q-p) := Int.natCast_dvd_natCast.mp (by
      push_cast
      rw [Int.ofNat_sub hpq]
      exact hdivI)
    have hmdiff := hc.dvd_of_dvd_mul_left hdiv
    by_contra hne
    have hpos : 0<q-p := by omega
    have hle := Nat.le_of_dvd hpos hmdiff
    omega
  have hp : p1=p2 := by
    rcases le_total p1 p2 with h | h
    · exact hstep p1 p2 n1 n2 h hp2 he1 he2
    · exact (hstep p2 p1 n2 n1 h hp1 he2 he1).symm
  refine ⟨hp,?_⟩
  apply Nat.eq_of_mul_eq_mul_left hm
  rw [hp] at he1
  omega

/-- The original UNSPLIT true-cell fibre, after fixing m and the complete
remaining source-weight factor B. The variable Q0 prime and genuine beta
prime are distinct coordinates. This is the original equation B*p+2=m*n;
in particular no false divisibility of n by a taken Q product is inserted. -/
def sourceNativeB572TrueBetaQ0Fibre434
    (d N i k m B : ℕ) (b c L : ℝ) : Finset (ℕ×ℕ) :=
  ((sourceOriginalQActualBands 6 d L ⟨0,by omega⟩) ×ˢ
    sourceNativeB572TrueBetaSet434 b c L N i k).filter
    (fun z => B*z.1+2=m*z.2)

/-- With the original D36 cofactor masks and actual Q0 band, an unsplit
true-beta fibre has at most one (Q0 prime, beta prime) pair. This is a
statement about the unsplit +2 equation, distinct from the two-endpoint
comparison fibre in B567. No nonempty fibre is postulated. -/
theorem source_native_B572_original_true_beta_fibre_card434
    (d N i j k m B : ℕ) (b c L : ℝ)
    (hbc : b<c) (hc : c≤1/2) (hi : i<N) (hL : 1≤L)
    (hWy : Real.exp (Real.sqrt L) ≤ (Real.exp L)^(sourceD31PrimeGrid b c N i))
    (hm : m ∈ sourceNativeB563OriginalD61ActiveK434
      (sourceD31PrimeGrid b c N i) (sourceD31PrimeGrid b c N (i+1)) b L j) :
    (sourceNativeB572TrueBetaQ0Fibre434 d N i k m B b c L).card ≤ 1 := by
  have hN : 0<N := by omega
  have heta := (B572_grid_mem b c N (i+1) hbc hN (by omega)).2.trans hc
  have hmR := (B572_active_support _ _ b L j m hWy hm).1
  have hW := B572_rough_scale_two L hL
  apply Finset.card_le_one.mpr
  intro z hz w hw
  obtain ⟨hzmem,hzeq⟩ := Finset.mem_filter.mp hz
  obtain ⟨hwmem,hweq⟩ := Finset.mem_filter.mp hw
  have hzQ := (Finset.mem_product.mp hzmem).1
  have hwQ := (Finset.mem_product.mp hwmem).1
  have hcop := B572_shift_two_coprime _ m B z.1 z.2 hmR hW hzeq
  have hzp := B572_Q0_lt_active d j m z.1 _ _ b L hL heta hWy hm hzQ
  have hwp := B572_Q0_lt_active d j m w.1 _ _ b L hL heta hWy hm hwQ
  obtain ⟨hp,hn⟩ := B572_prime_unique m B z.1 w.1 z.2 w.2 hmR.1 hcop hzp hwp hzeq hweq
  exact Prod.ext hp hn

private theorem B572_eventually_scale
    (b : ℝ) (hb : 0<b) :
    ∀ᶠ L : ℝ in atTop, 1≤L ∧ ∀ a : ℝ, b≤a →
      Real.exp (Real.sqrt L) ≤ (Real.exp L)^a := by
  filter_upwards [eventually_ge_atTop (max 1 ((1/b)^2))] with L hL
  have hLone : 1≤L := (le_max_left _ _).trans hL
  have hLpos : 0<L := by linarith
  have hLs : (1/b)^2≤L := (le_max_right _ _).trans hL
  have hroot : 1/b ≤ Real.sqrt L := by
    have hh := Real.sqrt_le_sqrt hLs
    simpa only [Real.sqrt_sq (by positivity : 0≤1/b)] using hh
  have hsqrt : Real.sqrt L ≤ b*L := by
    have hh := mul_le_mul_of_nonneg_right hroot (mul_nonneg hb.le (Real.sqrt_nonneg L))
    have hleft : (1/b)*(b*Real.sqrt L)=Real.sqrt L := by field_simp
    have hright : Real.sqrt L*(b*Real.sqrt L)=b*L := by
      nlinarith [Real.sq_sqrt hLpos.le]
    rwa [hleft,hright] at hh
  refine ⟨hLone,?_⟩
  intro a ha
  rw [← Real.exp_mul]
  apply Real.exp_le_exp.mpr
  have hmul := mul_le_mul_of_nonneg_right ha hLpos.le
  nlinarith

/-- For the SAME fixed positive prime-bin parameters, the only scalar
roughness/size thresholds used above are automatic eventually. All
actual bins, depths, beta/cofactor dyads and remaining source products
are quantified uniformly. No assumed product budget is used. -/
theorem eventually_source_native_B572_original_true_beta_fibre_card434
    (b c : ℝ) (hb : 0<b) (hbc : b<c) (hc : c≤1/2) :
    ∀ᶠ L : ℝ in atTop, ∀ d N i j k m B : ℕ, i<N →
      m ∈ sourceNativeB563OriginalD61ActiveK434
        (sourceD31PrimeGrid b c N i) (sourceD31PrimeGrid b c N (i+1)) b L j →
      (sourceNativeB572TrueBetaQ0Fibre434 d N i k m B b c L).card ≤ 1 := by
  filter_upwards [B572_eventually_scale b hb] with L hScale
  intro d N i j k m B hi hm
  have ha := (B572_grid_mem b c N i hbc (by omega) (by omega)).1
  exact source_native_B572_original_true_beta_fibre_card434
    d N i j k m B b c L hbc hc hi hScale.1 (hScale.2 _ ha) hm

/-- An occupied true-beta fibre contributes exactly ONE literal signed
original atom. Beta primality is an explicit conclusion, while the full
Delta, original Q/P weight and the same Psi are untouched. No positivity
or nonvanishing of this atom or of the complete true cell is inferred. -/
theorem source_native_B572_occupied_true_beta_atom434
    (d N i j k m B : ℕ) (b c L : ℝ) (Ψ : ℝ → ℝ)
    (hbc : b<c) (hc : c≤1/2) (hi : i<N) (hL : 1≤L) (hB : 0<B)
    (hWy : Real.exp (Real.sqrt L) ≤ (Real.exp L)^(sourceD31PrimeGrid b c N i))
    (hm : m ∈ sourceNativeB563OriginalD61ActiveK434
      (sourceD31PrimeGrid b c N i) (sourceD31PrimeGrid b c N (i+1)) b L j)
    (z0 : ℕ×ℕ) (hz0 : z0 ∈ sourceNativeB572TrueBetaQ0Fibre434 d N i k m B b c L) :
    z0.2.Prime ∧
    (∑ z ∈ sourceNativeB572TrueBetaQ0Fibre434 d N i k m B b c L,
      if 3 ≤ m*z.2 then
        sourceNativeB563OriginalD61Alpha434
          (sourceD31PrimeGrid b c N i) (sourceD31PrimeGrid b c N (i+1)) b L m *
          (originalWeight 6 (Real.exp L) (m*z.2-2)*
            Ψ (((m*z.2-2:ℕ):ℝ)/Real.exp L):ℝ) else 0) =
      sourceNativeB563OriginalD61Alpha434
        (sourceD31PrimeGrid b c N i) (sourceD31PrimeGrid b c N (i+1)) b L m *
        (originalWeight 6 (Real.exp L) (B*z0.1)*
          Ψ (((B*z0.1:ℕ):ℝ)/Real.exp L):ℝ) := by
  have hcard := source_native_B572_original_true_beta_fibre_card434
    d N i j k m B b c L hbc hc hi hL hWy hm
  obtain ⟨hzmem,hzeq⟩ := Finset.mem_filter.mp hz0
  have hzQ := (Finset.mem_product.mp hzmem).1
  have hzBeta := (Finset.mem_product.mp hzmem).2
  have hprime := (Finset.mem_filter.mp (Finset.mem_filter.mp hzBeta).2).2
  refine ⟨hprime,?_⟩
  have hset : sourceNativeB572TrueBetaQ0Fibre434 d N i k m B b c L = {z0} := by
    ext z
    constructor
    · intro hz
      exact Finset.mem_singleton.mpr ((Finset.card_le_one.mp hcard) z hz z0 hz0)
    · intro hz
      simpa only [Finset.mem_singleton.mp hz] using hz0
  have hp0 : 0<z0.1 := (sourceOriginalQActualBands_prime434 6 d L ⟨0,by omega⟩ z0.1 hzQ).pos
  have hbp : 0<B*z0.1 := Nat.mul_pos hB hp0
  have hguard : 3 ≤ m*z0.2 := by omega
  have hsub : m*z0.2-2=B*z0.1 := by omega
  rw [hset,Finset.sum_singleton,ite_eq_left hguard,hsub]


/-- A quantitative obstruction to inserting the free-Q0 progression
main term into an occupied TRUE beta fibre. The actual original band
has density at most exp(-9L/22) modulo the actual cofactor, yet an
occupied fibre has count one. This does not assert occupancy, a prime
progression theorem, or any lower bound for the full signed cell. -/
theorem source_native_B572_occupied_free_band_density_error434
    (d N i j k m B : ℕ) (b c L : ℝ)
    (hbc : b<c) (hc : c≤1/2) (hi : i<N) (hL : 1≤L)
    (hWy : Real.exp (Real.sqrt L) ≤ (Real.exp L)^(sourceD31PrimeGrid b c N i))
    (hm : m ∈ sourceNativeB563OriginalD61ActiveK434
      (sourceD31PrimeGrid b c N i) (sourceD31PrimeGrid b c N (i+1)) b L j)
    (z0 : ℕ×ℕ) (hz0 : z0 ∈ sourceNativeB572TrueBetaQ0Fibre434 d N i k m B b c L) :
    ((sourceOriginalQActualBands 6 d L ⟨0,by omega⟩).card:ℝ)/(m:ℝ) ≤
        Real.exp (-(9/22:ℝ)*L) ∧
    1-Real.exp (-(9/22:ℝ)*L) ≤
      ((sourceNativeB572TrueBetaQ0Fibre434 d N i k m B b c L).card:ℝ) -
        ((sourceOriginalQActualBands 6 d L ⟨0,by omega⟩).card:ℝ)/(m:ℝ) := by
  let Q := sourceOriginalQActualBands 6 d L ⟨0,by omega⟩
  have hsub : Q ⊆ Finset.Icc 1 ⌊Real.exp ((1/11:ℝ)*L)⌋₊ := by
    intro p hp
    have hpr := sourceOriginalQActualBands_prime434 6 d L ⟨0,by omega⟩ p hp
    have hUpper := (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).2
    have hUpper' : p ≤ ⌊Real.exp ((1/11:ℝ)*L)⌋₊ := by
      convert hUpper using 1
      norm_num [sourceOriginalQActualExponent,sourceOriginalQ0Scale]
    exact Finset.mem_Icc.mpr ⟨hpr.one_lt.le,hUpper'⟩
  have hcardNat : Q.card ≤ ⌊Real.exp ((1/11:ℝ)*L)⌋₊ := by
    simpa using Finset.card_le_card hsub
  have hcardReal : (Q.card:ℝ) ≤ Real.exp ((1/11:ℝ)*L) :=
    (Nat.le_floor_iff (Real.exp_nonneg _)).mp hcardNat
  have hSupport := B572_active_support _ _ b L j m hWy hm
  have hmpos : (0:ℝ) < m := by exact_mod_cast hSupport.1.1
  have heta := (B572_grid_mem b c N (i+1) hbc (by omega) (by omega)).2.trans hc
  have hmLower : Real.exp ((1/2:ℝ)*L) ≤ (m:ℝ) := by
    apply le_trans _ hSupport.2
    apply Real.exp_le_exp.mpr
    have hLp : 0≤L := by linarith
    exact mul_le_mul_of_nonneg_right (by linarith : (1/2:ℝ)≤1-sourceD31PrimeGrid b c N (i+1)) hLp
  have hdensity : (Q.card:ℝ)/(m:ℝ) ≤ Real.exp (-(9/22:ℝ)*L) := by
    apply (div_le_iff₀ hmpos).mpr
    calc
      (Q.card:ℝ) ≤ Real.exp ((1/11:ℝ)*L) := hcardReal
      _ = Real.exp (-(9/22:ℝ)*L)*Real.exp ((1/2:ℝ)*L) := by
        rw [← Real.exp_add]
        congr 1
        ring
      _ ≤ _ := by simpa only [mul_comm] using
        mul_le_mul_of_nonneg_left hmLower (Real.exp_nonneg (-(9/22:ℝ)*L))
  refine ⟨hdensity,?_⟩
  have hcard := source_native_B572_original_true_beta_fibre_card434
    d N i j k m B b c L hbc hc hi hL hWy hm
  have hpos : 0<(sourceNativeB572TrueBetaQ0Fibre434 d N i k m B b c L).card :=
    Finset.card_pos.mpr ⟨z0,hz0⟩
  have heq : (sourceNativeB572TrueBetaQ0Fibre434 d N i k m B b c L).card = 1 := by omega
  rw [heq]
  norm_num only [Nat.cast_one]
  exact sub_le_sub_left hdensity 1
end Green64Analytic.ShiftTwoTerminal

end

end

