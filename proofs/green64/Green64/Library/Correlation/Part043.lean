module

public import Green64.Library.Correlation.MemoryOmissionProduct
public import Mathlib.Logic.Equiv.Fintype
public import Green64.Library.Correlation.Part005
public import Green64.Library.Weights.Part024

@[expose] public section

/-!
# Correlation / Part043

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceOriginalMemoryOmissionPrimeFloor -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 4000000

theorem eventually_source_original_memory_omission_exponent_gap434
    (ell : ℕ) (C0 b c : ℝ) (hC0 : 0 ≤ C0) (hbc : b<c) :
    ∀ᶠ L : ℝ in atTop, 1 ≤ L ∧
      (ell:ℝ)*C0*Real.log L*L^b < L^c := by
  let delta := (c-b)/2
  have hd : 0 < delta := by dsimp [delta];linarith only [hbc]
  let K := (ell:ℝ)*C0/delta
  have hK : 0 ≤ K := div_nonneg (mul_nonneg (Nat.cast_nonneg _) hC0) hd.le
  have hEvent : ∀ᶠ L : ℝ in atTop,K+1 ≤ L^delta :=
    (tendsto_rpow_atTop hd).eventually (eventually_ge_atTop (K+1))
  filter_upwards [hEvent,eventually_ge_atTop (1:ℝ)] with L hLarge hL
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hlog := Real.log_le_rpow_div (x:=L) (ε:=delta) hLp.le hd
  refine ⟨hL,?_⟩
  calc
    _ ≤ ((ell:ℝ)*C0)*(L^delta/delta)*L^b :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hlog (mul_nonneg (Nat.cast_nonneg _) hC0))
        (Real.rpow_nonneg hLp.le _)
    _ = K*(L^delta*L^b) := by dsimp [K];ring
    _ < L^delta*(L^delta*L^b) :=
      mul_lt_mul_of_pos_right (by linarith only [hLarge])
        (mul_pos (Real.rpow_pos_of_pos hLp _) (Real.rpow_pos_of_pos hLp _))
    _ = L^c := by
      rw [← Real.rpow_add hLp,← Real.rpow_add hLp]
      congr 1
      dsimp [delta]
      ring

theorem source_original_memory_omission_log_upper434
    {ι : Type} [Fintype ι] (M ell : ℕ)
    (v : ι → Fin M → ℕ) (hv : ∀ g i,0<v g i)
    (O : ι → Finset (Fin M)) (hO : ∀ g,(O g).card=ell)
    (L b : ℝ) (hUpper : ∀ g i,(v g i:ℝ) ≤ Real.exp (L^b)) :
    Real.log ((∏ g : ι,∏ i ∈ O g,v g i:ℕ):ℝ) ≤
      (Fintype.card ι:ℝ)*(ell:ℝ)*L^b := by
  classical
  have hp (g : ι) (i : Fin M) : 0 < (v g i:ℝ) := Nat.cast_pos.mpr (hv g i)
  have hlog (g : ι) (i : Fin M) : Real.log (v g i:ℝ) ≤ L^b := by
    simpa only [Real.log_exp] using Real.log_le_log (hp g i) (hUpper g i)
  calc
    _ = ∑ g : ι,∑ i ∈ O g,Real.log (v g i:ℝ) := by
      simp_rw [Nat.cast_prod]
      rw [Real.log_prod]
      · apply Finset.sum_congr rfl
        intro g _
        exact Real.log_prod (fun i _ => (hp g i).ne')
      · intro g _
        exact (Finset.prod_pos (fun i _ => hp g i)).ne'
    _ ≤ ∑ g : ι,∑ _i ∈ O g,L^b :=
      Finset.sum_le_sum (fun g _ => Finset.sum_le_sum (fun i _ => hlog g i))
    _ = _ := by simp [hO];ring

/-- The true omitted SMALL product is below every BIG prime uniformly
in J/M and in all moving groups, by the original strict b<c gap. -/
theorem eventually_source_original_memory_actual_SMALL_omission_below_BIG434
    (cfg : SourceComparisonFixed434) (ell : ℕ) :
    ∀ᶠ L : ℝ in atTop,
    ∀ {ι G : Type} [Fintype ι] [DecidableEq ι] [Fintype G] [DecidableEq G]
      (x Y Hprime : ℝ) (data : SourceComparisonData434 ι G cfg x L Y Hprime)
      [∀ g (p : {p : ℕ // p ∈ data.Ts g}),NeZero p.val]
      (M : ℕ)
      (xs : Green64SmallHaar.GroupState (fun g => {p : ℕ // p ∈ data.Ts g})
        (fun _ p => p.val) M)
      (hSmallUpper : ∀ g,∀ p ∈ data.Ts g,(p:ℝ) ≤ Real.exp (L^cfg.bexp))
      (p : ℕ) (hp : Real.exp (L^cfg.cexp) ≤ (p:ℝ))
      (O : ι → {S : Finset (Fin M) // S.card=ell}),
    (∏ g : ι,∏ i ∈ (O g).val,
      (Green64SmallHaar.marks (fun p : {p : ℕ // p ∈ data.Ts g} => p.val)
        M (xs g) i).val) < p := by
  filter_upwards [eventually_source_original_memory_omission_exponent_gap434
    ell cfg.C0 cfg.bexp cfg.cexp cfg.hC0 cfg.hbc] with L hGap
  intro ι G instI instDI instG instDG x Y Hprime data instNZ M xs hSmallUpper p hp O
  classical
  let v : ι → Fin M → ℕ := fun g i =>
    (Green64SmallHaar.marks (fun p : {p : ℕ // p ∈ data.Ts g} => p.val) M (xs g) i).val
  have hv (g : ι) (i : Fin M) : 0<v g i :=
    (data.hTsPrime g _ (Green64SmallHaar.marks
      (fun p : {p : ℕ // p ∈ data.Ts g} => p.val) M (xs g) i).property).pos
  have hUpper (g : ι) (i : Fin M) : (v g i:ℝ) ≤ Real.exp (L^cfg.bexp) :=
    hSmallUpper g _ (Green64SmallHaar.marks
      (fun p : {p : ℕ // p ∈ data.Ts g} => p.val) M (xs g) i).property
  let U := ∏ g : ι,∏ i ∈ (O g).val,v g i
  have hU : 0 < (U:ℝ) := Nat.cast_pos.mpr
    (Finset.prod_pos (fun g _ => Finset.prod_pos (fun i _ => hv g i)))
  have hlog := source_original_memory_omission_log_upper434 M ell v hv
    (fun g => (O g).val) (fun g => (O g).property) L cfg.bexp hUpper
  have hGroups :
      (Fintype.card ι:ℝ)*(ell:ℝ)*L^cfg.bexp ≤
        (ell:ℝ)*cfg.C0*Real.log L*L^cfg.bexp := by
    have hh := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right data.hSmallGroups (Nat.cast_nonneg ell))
      (Real.rpow_nonneg (zero_le_one.trans hGap.1) cfg.bexp)
    simpa only [mul_assoc,mul_left_comm,mul_comm] using hh
  have he : (U:ℝ) < Real.exp (L^cfg.cexp) := by
    rw [← Real.exp_log hU]
    exact Real.exp_lt_exp.mpr (hlog.trans_lt (hGroups.trans_lt hGap.2))
  exact_mod_cast he.trans_le hp
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalMemoryPromotionOmissionCount -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 5000000

/-- Uniform arithmetic count for the literal SMALL omission family and all
ordered OLD particles. The nonzero congruence coefficients are explicit.
This is a count of exceptional omission tuples, not a weighted DIRTY norm. -/
theorem eventually_source_original_memory_actual_SMALL_OLD_omission_count434
    (cfg : SourceComparisonFixed434) (ell : ℕ) :
    ∀ᶠ L : ℝ in atTop,
    ∀ {ι G : Type} [Fintype ι] [DecidableEq ι] [Fintype G] [DecidableEq G]
      (x Y Hprime : ℝ) (data : SourceComparisonData434 ι G cfg x L Y Hprime)
      (sep : SourceOriginalSource03GroupSeparation434 data)
      [∀ g (p : {p : ℕ // p ∈ data.Ts g}),NeZero p.val]
      (M : ℕ)
      (xs : Green64SmallHaar.GroupState (fun g => {p : ℕ // p ∈ data.Ts g})
        (fun _ p => p.val) M)
      (hSmallUpper : ∀ g,∀ p ∈ data.Ts g,(p:ℝ) ≤ Real.exp (L^cfg.bexp))
      (hBigLower : ∀ g,∀ p ∈ data.Tb g,Real.exp (L^cfg.cexp) ≤ (p:ℝ))
      (sizes : G → ℕ)
      (prime : (g : G) → Fin (sizes g) → {p : ℕ // p ∈ data.Tb g})
      (r A : (j : Σ g : G,Fin (sizes g)) → ZMod (prime j.1 j.2).val)
      (hA : ∀ j,A j ≠ 0),
    let choices := ι → {S : Finset (Fin M) // S.card=ell}
    let U := fun O : choices => ∏ g : ι,∏ i ∈ (O g).val,
      (Green64SmallHaar.marks (fun p : {p : ℕ // p ∈ data.Ts g} => p.val)
        M (xs g) i).val
    ((Finset.univ : Finset choices).filter
      (fun O => ∃ j : Σ g : G,Fin (sizes g),
        r j*(U O:ZMod (prime j.1 j.2).val)+A j=0)).card ≤ ∑ g : G,sizes g := by
  filter_upwards [eventually_source_original_memory_actual_SMALL_omission_below_BIG434
    cfg ell] with L hFloor
  intro ι G instI instDI instG instDG x Y Hprime data sep instNZ
    M xs hSmallUpper hBigLower sizes prime r A hA
  classical
  let choices := ι → {S : Finset (Fin M) // S.card=ell}
  let I := Σ g : G,Fin (sizes g)
  let U := fun O : choices => ∏ g : ι,∏ i ∈ (O g).val,
    (Green64SmallHaar.marks (fun p : {p : ℕ // p ∈ data.Ts g} => p.val)
      M (xs g) i).val
  let bad := fun j : I => (Finset.univ : Finset choices).filter
    (fun O => r j*(U O:ZMod (prime j.1 j.2).val)+A j=0)
  have hOne (j : I) : (bad j).card ≤ 1 := by
    apply source_original_memory_actual_SMALL_one_promotion_choice434
      data sep M ell xs (prime j.1 j.2).val
      (data.hTbPrime j.1 _ (prime j.1 j.2).property) (r j) (A j) (hA j)
    intro O
    exact hFloor x Y Hprime data M xs hSmallUpper _ 
      (hBigLower j.1 _ (prime j.1 j.2).property) O
  have hUnion :
      ((Finset.univ : Finset choices).filter
        (fun O => ∃ j : I,r j*(U O:ZMod (prime j.1 j.2).val)+A j=0)) =
      (Finset.univ : Finset I).biUnion bad := by
    ext O
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_biUnion,bad]
  change ((Finset.univ : Finset choices).filter
    (fun O => ∃ j : I,r j*(U O:ZMod (prime j.1 j.2).val)+A j=0)).card ≤ _
  rw [hUnion]
  calc
    _ ≤ ∑ j : I,(bad j).card := Finset.card_biUnion_le
    _ ≤ ∑ _j : I,1 := Finset.sum_le_sum (fun j _ => hOne j)
    _ = ∑ g : G,sizes g := by simp [I,Fintype.card_sigma]
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalMemoryPromotionCoefficient -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 6000000

/-- The full actual SMALL product is a unit modulo every actual BIG prime,
by prime group separation. No probabilistic or analytic premise is used. -/
theorem source_original_memory_actual_SMALL_full_product_nonzero434
    {ι G : Type} [Fintype ι] [DecidableEq ι] [Fintype G] [DecidableEq G]
    {cfg : SourceComparisonFixed434} {x L Y Hprime : ℝ}
    (data : SourceComparisonData434 ι G cfg x L Y Hprime)
    (sep : SourceOriginalSource03GroupSeparation434 data)
    [∀ g (p : {p : ℕ // p ∈ data.Ts g}),NeZero p.val]
    (M : ℕ)
    (xs : Green64SmallHaar.GroupState (fun g => {p : ℕ // p ∈ data.Ts g})
      (fun _ p => p.val) M)
    (g : G) (p : {p : ℕ // p ∈ data.Tb g}) :
    ((∏ i : ι,∏ j : Fin M,
      (Green64SmallHaar.marks (fun p : {p : ℕ // p ∈ data.Ts i} => p.val)
        M (xs i) j).val : ℕ):ZMod p.val) ≠ 0 := by
  classical
  have hp : p.val.Prime := data.hTbPrime g p.val p.property
  letI : Fact p.val.Prime := ⟨hp⟩
  simp only [Nat.cast_prod]
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  apply Finset.prod_ne_zero_iff.mpr
  intro j _
  let a := Green64SmallHaar.marks
    (fun p : {p : ℕ // p ∈ data.Ts i} => p.val) M (xs i) j
  have ha : a.val.Prime := data.hTsPrime i a.val a.property
  have hnd : ¬ p.val ∣ a.val := by
    intro h
    have he : p.val=a.val := (Nat.prime_dvd_prime_iff_eq hp ha).mp h
    exact sep.hTB i g a.val a.property (he ▸ p.property)
  exact fun hz => hnd ((ZMod.natCast_eq_zero_iff a.val p.val).mp hz)

/-- The original oriented coefficient is nonzero whenever the promoted
prime does not divide the BIG divisor and the signed mode is below it. -/
theorem source_original_memory_oriented_promotion_coefficient_nonzero434
    (p F DB : ℕ) (hp : p.Prime) (hF : (F:ZMod p) ≠ 0)
    (hDB : ¬ p ∣ DB) (o k : ℤ) (ho : o=1 ∨ o= -1)
    (hk : k ≠ 0) (hkp : k.natAbs<p) :
    ((o*k*(DB*F:ℕ):ℤ):ZMod p) ≠ 0 := by
  letI : Fact p.Prime := ⟨hp⟩
  have hkZ : (k:ZMod p) ≠ 0 := by
    intro he
    have hd : p ∣ k.natAbs := Int.natCast_dvd.mp
      ((ZMod.intCast_zmod_eq_zero_iff_dvd k p).mp he)
    exact (not_le_of_gt hkp) (Nat.le_of_dvd (Int.natAbs_pos.mpr hk) hd)
  have hoZ : (o:ZMod p) ≠ 0 := by
    rcases ho with ho | ho <;> simp [ho]
  have hDBZ : (DB:ZMod p) ≠ 0 :=
    fun he => hDB ((ZMod.natCast_eq_zero_iff DB p).mp he)
  push_cast
  exact mul_ne_zero (mul_ne_zero hoZ hkZ) (mul_ne_zero hDBZ hF)

/-- Every fixed polynomial mode range is strictly below the original
exponential BIG-prime floor, uniformly in the moving data. -/
theorem eventually_source_original_memory_mode_below_BIG434
    (cfg : SourceComparisonFixed434) (Ck : ℝ) :
    ∀ᶠ L : ℝ in atTop,1 ≤ L ∧ L^Ck < Real.exp (L^cfg.cexp) := by
  have hc : 0 < cfg.cexp := cfg.haexp.trans (cfg.hab.trans cfg.hbc)
  filter_upwards [eventually_source_original_memory_omission_exponent_gap434
    1 (max Ck 0) 0 cfg.cexp (le_max_right _ _) hc] with L h
  have hLp : 0 < L := zero_lt_one.trans_le h.1
  refine ⟨h.1,?_⟩
  have hlog : Ck*Real.log L < L^cfg.cexp := by
    have hh : max Ck 0 * Real.log L < L^cfg.cexp := by simpa using h.2
    exact (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.log_nonneg h.1)).trans_lt hh
  rw [Real.rpow_def_of_pos hLp]
  exact Real.exp_lt_exp.mpr (by simpa only [mul_comm] using hlog)

/-- At most one genuine SMALL omission tuple can promote a fixed actual
OLD prime/residue for the literal step o*k*(Dsmall*Dbig).
Both the coefficient nonvanishing and the prime floor are proved from
the actual physical hypotheses. The remaining permutation and weighted
DIRTY transfers are separate obligations. -/
theorem eventually_source_original_memory_literal_promotion_omission_count434
    (cfg : SourceComparisonFixed434) (ell : ℕ) (Ck : ℝ) :
    ∀ᶠ L : ℝ in atTop,
    ∀ {ι G : Type} [Fintype ι] [DecidableEq ι] [Fintype G] [DecidableEq G]
      (x Y Hprime : ℝ) (data : SourceComparisonData434 ι G cfg x L Y Hprime)
      (sep : SourceOriginalSource03GroupSeparation434 data)
      [∀ g (p : {p : ℕ // p ∈ data.Ts g}),NeZero p.val]
      (M : ℕ)
      (xs : Green64SmallHaar.GroupState (fun g => {p : ℕ // p ∈ data.Ts g})
        (fun _ p => p.val) M)
      (hSmallUpper : ∀ g,∀ p ∈ data.Ts g,(p:ℝ) ≤ Real.exp (L^cfg.bexp))
      (g : G) (p : {p : ℕ // p ∈ data.Tb g})
      (hpFloor : Real.exp (L^cfg.cexp) ≤ (p.val:ℝ))
      (DB : ℕ) (r : ZMod p.val) (o k : ℤ)
      (ho : o=1 ∨ o= -1) (hk0 : k ≠ 0) (hk : (k.natAbs:ℝ) ≤ L^Ck),
    let choices := ι → {S : Finset (Fin M) // S.card=ell}
    let DS := fun O : choices => ∏ i : ι,∏ j ∈ (O i).valᶜ,
      (Green64SmallHaar.marks (fun p : {p : ℕ // p ∈ data.Ts i} => p.val)
        M (xs i) j).val
    ((Finset.univ : Finset choices).filter (fun O =>
      ¬ p.val ∣ DS O*DB ∧ r+((o*k*(DS O*DB:ℕ):ℤ):ZMod p.val)=0)).card ≤ 1 := by
  filter_upwards [eventually_source_original_memory_actual_SMALL_omission_below_BIG434 cfg ell,
    eventually_source_original_memory_mode_below_BIG434 cfg Ck] with L hFloor hMode
  intro ι G instI instDI instG instDG x Y Hprime data sep instNZ
    M xs hSmallUpper g p hpFloor DB r o k ho hk0 hk
  classical
  let choices := ι → {S : Finset (Fin M) // S.card=ell}
  let v := fun (i : ι) (j : Fin M) =>
    (Green64SmallHaar.marks (fun p : {p : ℕ // p ∈ data.Ts i} => p.val) M (xs i) j).val
  let U := fun O : choices => ∏ i : ι,∏ j ∈ (O i).val,v i j
  let DS := fun O : choices => ∏ i : ι,∏ j ∈ (O i).valᶜ,v i j
  let F := ∏ i : ι,∏ j : Fin M,v i j
  have hprod (O : choices) : U O * DS O = F := by
    dsimp only [U,DS,F]
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i _
    exact Finset.prod_mul_prod_compl (O i).val (v i)
  have hF : (F:ZMod p.val) ≠ 0 :=
    source_original_memory_actual_SMALL_full_product_nonzero434 data sep M xs g p
  have hkp : k.natAbs < p.val := by
    exact_mod_cast hk.trans_lt (hMode.2.trans_le hpFloor)
  change ((Finset.univ : Finset choices).filter (fun O =>
    ¬ p.val ∣ DS O*DB ∧ r+((o*k*(DS O*DB:ℕ):ℤ):ZMod p.val)=0)).card ≤ 1
  apply Finset.card_le_one.mpr
  intro O hO T hT
  have ho' := (Finset.mem_filter.mp hO).2
  have ht' := (Finset.mem_filter.mp hT).2
  have hDB : ¬ p.val ∣ DB := fun hd => ho'.1 (dvd_mul_of_dvd_right hd _)
  have hp := data.hTbPrime g p.val p.property
  have hA := source_original_memory_oriented_promotion_coefficient_nonzero434
    p.val F DB hp hF hDB o k ho hk0 hkp
  have he := source_original_memory_one_particle_omission_unique434 p.val hp r _
    hA (U O) (U T)
    (hFloor x Y Hprime data M xs hSmallUpper p.val hpFloor O)
    (hFloor x Y Hprime data M xs hSmallUpper p.val hpFloor T)
    (source_original_memory_promotion_omission_equation434 p.val F (U O) (DS O) DB o k r
      (hprod O) ho'.2)
    (source_original_memory_promotion_omission_equation434 p.val F (U T) (DS T) DB o k r
      (hprod T) ht'.2)
  have hf := source_original_memory_actual_SMALL_group_omission_injective434 data sep M xs he
  funext i
  exact Subtype.ext (congrFun hf i)
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalMemoryLiteralPromotionCount -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 5000000

/-- The actual original promotion congruence excludes at most the number
of ordered OLD particles among the genuine SMALL omission tuples.
The result is uniform before M, all OLD sizes, all prime labels and all
admissible signed modes. It is an arithmetic count, not a weighted norm. -/
theorem eventually_source_original_memory_literal_ALL_OLD_promotion_count434
    (cfg : SourceComparisonFixed434) (ell : ℕ) (Ck : ℝ) :
    ∀ᶠ L : ℝ in atTop,
    ∀ {ι G : Type} [Fintype ι] [DecidableEq ι] [Fintype G] [DecidableEq G]
      (x Y Hprime : ℝ) (data : SourceComparisonData434 ι G cfg x L Y Hprime)
      (sep : SourceOriginalSource03GroupSeparation434 data)
      [∀ g (p : {p : ℕ // p ∈ data.Ts g}),NeZero p.val]
      (M : ℕ)
      (xs : Green64SmallHaar.GroupState (fun g => {p : ℕ // p ∈ data.Ts g})
        (fun _ p => p.val) M)
      (hSmallUpper : ∀ g,∀ p ∈ data.Ts g,(p:ℝ) ≤ Real.exp (L^cfg.bexp))
      (hBigLower : ∀ g,∀ p ∈ data.Tb g,Real.exp (L^cfg.cexp) ≤ (p:ℝ))
      (sizes : G → ℕ)
      (prime : (g : G) → Fin (sizes g) → {p : ℕ // p ∈ data.Tb g})
      (r : (j : Σ g : G,Fin (sizes g)) → ZMod (prime j.1 j.2).val)
      (DB : ℕ) (o k : ℤ) (ho : o=1 ∨ o= -1) (hk0 : k ≠ 0)
      (hk : (k.natAbs:ℝ) ≤ L^Ck),
    let choices := ι → {S : Finset (Fin M) // S.card=ell}
    let DS := fun O : choices => ∏ g : ι,∏ i ∈ (O g).valᶜ,
      (Green64SmallHaar.marks (fun p : {p : ℕ // p ∈ data.Ts g} => p.val)
        M (xs g) i).val
    ((Finset.univ : Finset choices).filter
      (fun O => ∃ j : Σ g : G,Fin (sizes g),
        ¬ (prime j.1 j.2).val ∣ DS O*DB ∧
          r j+((o*k*(DS O*DB:ℕ):ℤ):ZMod (prime j.1 j.2).val)=0)).card ≤
      ∑ g : G,sizes g := by
  filter_upwards [eventually_source_original_memory_literal_promotion_omission_count434
    cfg ell Ck] with L hOneEvent
  intro ι G instI instDI instG instDG x Y Hprime data sep instNZ M xs
    hSmallUpper hBigLower sizes prime r DB o k ho hk0 hk
  classical
  let choices := ι → {S : Finset (Fin M) // S.card=ell}
  let I := Σ g : G,Fin (sizes g)
  let DS := fun O : choices => ∏ g : ι,∏ i ∈ (O g).valᶜ,
    (Green64SmallHaar.marks (fun p : {p : ℕ // p ∈ data.Ts g} => p.val)
      M (xs g) i).val
  let hit := fun (O : choices) (j : I) =>
    ¬ (prime j.1 j.2).val ∣ DS O*DB ∧
      r j+((o*k*(DS O*DB:ℕ):ℤ):ZMod (prime j.1 j.2).val)=0
  let bad := fun j : I => (Finset.univ : Finset choices).filter (fun O => hit O j)
  have hOne (j : I) : (bad j).card ≤ 1 :=
    hOneEvent x Y Hprime data sep M xs hSmallUpper j.1 (prime j.1 j.2)
      (hBigLower j.1 _ (prime j.1 j.2).property) DB (r j) o k ho hk0 hk
  have hUnion : ((Finset.univ : Finset choices).filter
      (fun O => ∃ j : I,hit O j)) = (Finset.univ : Finset I).biUnion bad := by
    ext O
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_biUnion,bad]
  change ((Finset.univ : Finset choices).filter (fun O => ∃ j : I,hit O j)).card ≤ _
  rw [hUnion]
  calc
    _ ≤ ∑ j : I,(bad j).card := Finset.card_biUnion_le
    _ ≤ ∑ _j : I,1 := Finset.sum_le_sum (fun j _ => hOne j)
    _ = ∑ g : G,sizes g := by simp [I,Fintype.card_sigma]
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalMemoryOmissionPermutation -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 5000000

/-- Exact finite change of a uniform measure through equal fibers. -/
theorem source_original_memory_uniform_fiber_average434
    {A B : Type} [Fintype A] [Fintype B] [Nonempty A]
    (f : A → B)
    (hcard : ∀ b c : B,Nat.card {a : A // f a=b} =
      Nat.card {a : A // f a=c})
    (w : B → ℝ) :
    (∑ a : A,w (f a))/(Fintype.card A:ℝ) =
      (∑ b : B,w b)/(Fintype.card B:ℝ) := by
  classical
  let a0 : A := Classical.choice inferInstance
  let b0 : B := f a0
  let c : ℕ := Fintype.card {a : A // f a=b0}
  have hc : 0<c := by
    apply Fintype.card_pos_iff.mpr
    exact ⟨⟨a0,rfl⟩⟩
  have hcb (b : B) : Fintype.card {a : A // f a=b}=c := by
    simpa only [Nat.card_eq_fintype_card] using hcard b b0
  have htotal : (Fintype.card A:ℝ)=(Fintype.card B:ℝ)*(c:ℝ) := by
    have hh := Fintype.sum_fiberwise' f (fun _ : B => (1:ℝ))
    simpa [hcb] using hh.symm
  have hsum : (∑ a : A,w (f a))=(c:ℝ)*∑ b : B,w b := by
    rw [← Fintype.sum_fiberwise' f w]
    simp_rw [Finset.sum_const,Finset.card_univ,hcb,nsmul_eq_mul]
    exact (Finset.mul_sum _ _ _).symm
  rw [hsum,htotal]
  have hc0 : (c:ℝ) ≠ 0 := (Nat.cast_pos.mpr hc).ne'
  field_simp

/-- The actual source permutation omits the permuted complement of the
literal sourceSmallShared set, with exactly ell slots per SMALL group. -/
def sourceOriginalMemoryOmissionTuple434
    {SG : Type} [Fintype SG] (J ell : ℕ)
    (sigma : SG → Equiv.Perm (Fin (J+ell))) :
    SG → {S : Finset (Fin (J+ell)) // S.card=ell} :=
  fun g => ⟨(sourceSmallShared J ell g)ᶜ |>.map (sigma g).toEmbedding,by
    rw [Finset.card_map,Finset.card_compl,
      source_original_B26_small_shared_card434 J ell g]
    simp⟩

/-- The fibers of the actual simultaneous SMALL source permutation map
have equal cardinal, including the full growing family of groups. -/
theorem source_original_memory_omission_permutation_fibers434
    {SG : Type} [Fintype SG] (J ell : ℕ)
    (O T : SG → {S : Finset (Fin (J+ell)) // S.card=ell}) :
    Nat.card {sigma : SG → Equiv.Perm (Fin (J+ell)) //
      sourceOriginalMemoryOmissionTuple434 J ell sigma=O} =
    Nat.card {sigma : SG → Equiv.Perm (Fin (J+ell)) //
      sourceOriginalMemoryOmissionTuple434 J ell sigma=T} := by
  classical
  have hex (g : SG) : ∃ pi : Equiv.Perm (Fin (J+ell)),
      (O g).val.map pi.toEmbedding=(T g).val :=
    Equiv.Perm.exists_map_finset_eq _ _ ((O g).property.trans (T g).property.symm)
  choose pi hpi using hex
  have hpi' (g : SG) : (T g).val.map (pi g).symm.toEmbedding=(O g).val := by
    rw [← hpi g]
    simp [Finset.map_map]
  let e :
      {sigma : SG → Equiv.Perm (Fin (J+ell)) //
        sourceOriginalMemoryOmissionTuple434 J ell sigma=O} ≃
      {sigma : SG → Equiv.Perm (Fin (J+ell)) //
        sourceOriginalMemoryOmissionTuple434 J ell sigma=T} :=
    { toFun := fun s => ⟨fun g => (s.val g).trans (pi g),by
        funext g
        apply Subtype.ext
        have hs := congrArg Subtype.val (congrFun s.property g)
        dsimp only [sourceOriginalMemoryOmissionTuple434] at hs
        change ((sourceSmallShared J ell g)ᶜ).map ((s.val g).trans (pi g)).toEmbedding =
          (T g).val
        calc
          _ = (((sourceSmallShared J ell g)ᶜ).map (s.val g).toEmbedding).map
              (pi g).toEmbedding := by simp [Finset.map_map]
          _ = (T g).val := by rw [hs,hpi g]⟩
      invFun := fun s => ⟨fun g => (s.val g).trans (pi g).symm,by
        funext g
        apply Subtype.ext
        have hs := congrArg Subtype.val (congrFun s.property g)
        dsimp only [sourceOriginalMemoryOmissionTuple434] at hs
        change ((sourceSmallShared J ell g)ᶜ).map
          ((s.val g).trans (pi g).symm).toEmbedding = (O g).val
        calc
          _ = (((sourceSmallShared J ell g)ᶜ).map (s.val g).toEmbedding).map
              (pi g).symm.toEmbedding := by simp [Finset.map_map]
          _ = (O g).val := by rw [hs,hpi' g]⟩
      left_inv := by intro s;apply Subtype.ext;funext g;ext i;simp
      right_inv := by intro s;apply Subtype.ext;funext g;ext i;simp }
  exact Nat.card_congr e

/-- Exact normalized source-permutation average over genuine omitted
ell-subsets in every SMALL group. No permutation count is lost. -/
theorem source_original_memory_omission_permutation_average434
    {SG : Type} [Fintype SG] (J ell : ℕ)
    (w : (SG → {S : Finset (Fin (J+ell)) // S.card=ell}) → ℝ) :
    (∑ sigma : SG → Equiv.Perm (Fin (J+ell)),
      w (sourceOriginalMemoryOmissionTuple434 J ell sigma)) /
        (((J+ell).factorial:ℝ)^(Fintype.card SG)) =
    (∑ O : SG → {S : Finset (Fin (J+ell)) // S.card=ell},w O) /
        (((J+ell).choose ell:ℝ)^(Fintype.card SG)) := by
  have hh := source_original_memory_uniform_fiber_average434
    (sourceOriginalMemoryOmissionTuple434 (SG:=SG) J ell)
    (source_original_memory_omission_permutation_fibers434 J ell) w
  simpa [Fintype.card_fun,Fintype.card_perm,Fintype.card_finset_len] using hh
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalMemoryOutputDamping -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 4000000

variable {P : Type} [Fintype P] [DecidableEq P]
variable (modulus : P → ℕ) [∀ p,NeZero (modulus p)] (M B : ℕ)

/-- Zero residues among the literal ordered survivors are exactly the
translated OLD zero indices minus the chosen promotion indices.
Numerical coincidences are never deduplicated. -/
theorem source_original_memory_survivor_zero_count434
    (x : BigState modulus M B) (step : ℤ)
    (c : BigEdgeChoice modulus M B x) :
    (survivors modulus M B x step c).countP (fun z => z.2=0) =
      (memoryTranslatedOldZero modulus M B x step \ selectedOld modulus M B x c).card := by
  classical
  let R := survivorIndices modulus M B x c
  let pred := fun i : Fin x.2.1.val =>
    (x.2.2 i).2+(step:ZMod (modulus (x.2.2 i).1))=0
  have hh := List.Nodup.card_eq_countP (P:=pred) (Finset.nodup_toList R)
  have hf : R.filter pred =
      memoryTranslatedOldZero modulus M B x step \ selectedOld modulus M B x c := by
    ext i
    simp only [R,pred,survivorIndices,memoryTranslatedOldZero,
      Finset.mem_filter,Finset.mem_sdiff,Finset.mem_univ,true_and]
    tauto
  calc
    _ = R.toList.countP pred := by
      simp only [survivors,List.countP_map,Function.comp_def,
        Green64PhysicalEdge.translateAtom]
      rfl
    _ = (R.filter pred).card := by simpa using hh.symm
    _ = _ := congrArg Finset.card hf

/-- Each selected OLD index can remove at most one translated zero.
Actual stored particles can only increase the output zero count. -/
theorem source_original_memory_output_zero_lower434
    (x : BigState modulus M B) (sigma : Equiv.Perm (Fin M)) (step : ℤ)
    (c : BigEdgeChoice modulus M B x) :
    (memoryTranslatedOldZero modulus M B x step).card-c.2.1.card ≤
      outputZeroCount modulus M B x sigma step c := by
  have hh := Finset.le_card_sdiff
    (selectedOld modulus M B x c) (memoryTranslatedOldZero modulus M B x step)
  rw [selectedOld_card modulus M B x c] at hh
  unfold outputZeroCount physicalPendingOutput
  rw [List.countP_append,source_original_memory_survivor_zero_count434]
  omega

/-- The actual input/output rho factors dominate the already checked
ordered retrieval damping expression, with all stores retained. -/
theorem source_original_memory_actual_branch_damping434
    (x : BigState modulus M B) (sigma : Equiv.Perm (Fin M)) (step : ℤ)
    (c : BigEdgeChoice modulus M B x)
    (rho : ℝ) (hr : 0 ≤ rho) (hr1 : rho ≤ 1) :
    rho^(Green64PhysicalEdge.oldZeroCount x.2+
      outputZeroCount modulus M B x sigma step c) ≤
      rho^((memoryTranslatedOldZero modulus M B x step).card-c.2.1.card) := by
  have hh := source_original_memory_output_zero_lower434 modulus M B x sigma step c
  exact pow_le_pow_of_le_one hr hr1 (hh.trans (Nat.le_add_left _ _))

/-- Sum the literal original input/output damping over every eligible
ordered retrieval injection. The bound is independent of M and OLD length
when the number of promoted slots is at most fixed d. -/
theorem source_original_memory_actual_retrieval_damping_sum434
    (x : BigState modulus M B) (sigma : Equiv.Perm (Fin M)) (step : ℤ)
    (S A : Finset (Fin M))
    (rho : ℝ) (hr : 0 < rho) (hr1 : rho < 1) (d : ℕ) (hA : A.card ≤ d) :
    (∑ f ∈ (Finset.univ : Finset (↥A ↪ Fin x.2.1.val)).filter
      (fun f => ∀ a,f a ∈ memoryTranslatedOldZero modulus M B x step),
      rho^(Green64PhysicalEdge.oldZeroCount x.2+
        outputZeroCount modulus M B x sigma step (S,⟨A,f⟩))) ≤
      memoryPromotionDampingConstant rho d := by
  calc
    _ ≤ ∑ f ∈ (Finset.univ : Finset (↥A ↪ Fin x.2.1.val)).filter
        (fun f => ∀ a,f a ∈ memoryTranslatedOldZero modulus M B x step),
        rho^((memoryTranslatedOldZero modulus M B x step).card-A.card) := by
      apply Finset.sum_le_sum
      intro f hf
      exact source_original_memory_actual_branch_damping434 modulus M B x sigma step
        (S,⟨A,f⟩) rho hr.le hr1.le
    _ ≤ _ := memory_actual_promotion_sum_bound modulus M B x step A rho hr hr1 d hA
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalMemoryPermutationPromotion -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 6000000

/-- The complement of the permuted omission tuple gives exactly the
literal permuted source SMALL shared divisor. -/
theorem source_original_memory_omission_complement_product434
    {SG : Type} [Fintype SG] (J ell : ℕ)
    (v : SG → Fin (J+ell) → ℕ)
    (sigma : SG → Equiv.Perm (Fin (J+ell))) :
    (∏ g : SG,∏ i ∈ (sourceOriginalMemoryOmissionTuple434 J ell sigma g).valᶜ,v g i) =
      ∏ g : SG,∏ i ∈ sourceSmallShared J ell g,v g (sigma g i) := by
  classical
  apply Finset.prod_congr rfl
  intro g _
  have hs : (sourceOriginalMemoryOmissionTuple434 J ell sigma g).valᶜ =
      (sourceSmallShared J ell g).map (sigma g).toEmbedding := by
    ext i
    simp only [sourceOriginalMemoryOmissionTuple434,Finset.mem_compl,
      Finset.mem_map_equiv,not_not]
  rw [hs,Finset.prod_map]
  rfl

/-- Applicable arithmetic rare-promotion probability under the actual
normalized SMALL source permutation measure. All ordered OLD particles,
the original sign and the nondivisibility condition are preserved. -/
theorem eventually_source_original_memory_literal_permutation_promotion_bound434
    (cfg : SourceComparisonFixed434) (ell : ℕ) (Ck : ℝ) :
    ∀ᶠ L : ℝ in atTop,
    ∀ {ι G : Type} [Fintype ι] [DecidableEq ι] [Fintype G] [DecidableEq G]
      (x Y Hprime : ℝ) (data : SourceComparisonData434 ι G cfg x L Y Hprime)
      (sep : SourceOriginalSource03GroupSeparation434 data)
      [∀ g (p : {p : ℕ // p ∈ data.Ts g}),NeZero p.val]
      (J : ℕ)
      (xs : Green64SmallHaar.GroupState (fun g => {p : ℕ // p ∈ data.Ts g})
        (fun _ p => p.val) (J+ell))
      (hSmallUpper : ∀ g,∀ p ∈ data.Ts g,(p:ℝ) ≤ Real.exp (L^cfg.bexp))
      (hBigLower : ∀ g,∀ p ∈ data.Tb g,Real.exp (L^cfg.cexp) ≤ (p:ℝ))
      (sizes : G → ℕ)
      (prime : (g : G) → Fin (sizes g) → {p : ℕ // p ∈ data.Tb g})
      (r : (j : Σ g : G,Fin (sizes g)) → ZMod (prime j.1 j.2).val)
      (DB : ℕ) (o k : ℤ) (ho : o=1 ∨ o= -1) (hk0 : k ≠ 0)
      (hk : (k.natAbs:ℝ) ≤ L^Ck),
    let DS := fun sigma : ι → Equiv.Perm (Fin (J+ell)) =>
      ∏ g : ι,∏ i ∈ sourceSmallShared J ell g,
        (Green64SmallHaar.marks (fun p : {p : ℕ // p ∈ data.Ts g} => p.val)
          (J+ell) (xs g) (sigma g i)).val
    (∑ sigma : ι → Equiv.Perm (Fin (J+ell)),
      if ∃ j : Σ g : G,Fin (sizes g),
        ¬ (prime j.1 j.2).val ∣ DS sigma*DB ∧
          r j+((o*k*(DS sigma*DB:ℕ):ℤ):ZMod (prime j.1 j.2).val)=0
      then (1:ℝ) else 0) / (((J+ell).factorial:ℝ)^(Fintype.card ι)) ≤
      ((∑ g : G,sizes g:ℕ):ℝ) /
        (((J+ell).choose ell:ℝ)^(Fintype.card ι)) := by
  filter_upwards [eventually_source_original_memory_literal_ALL_OLD_promotion_count434
    cfg ell Ck] with L hCountEvent
  intro ι G instI instDI instG instDG x Y Hprime data sep instNZ J xs
    hSmallUpper hBigLower sizes prime r DB o k ho hk0 hk
  classical
  let choices := ι → {S : Finset (Fin (J+ell)) // S.card=ell}
  let v := fun (g : ι) (i : Fin (J+ell)) =>
    (Green64SmallHaar.marks (fun p : {p : ℕ // p ∈ data.Ts g} => p.val)
      (J+ell) (xs g) i).val
  let DS := fun O : choices => ∏ g : ι,∏ i ∈ (O g).valᶜ,v g i
  let Ds := fun sigma : ι → Equiv.Perm (Fin (J+ell)) =>
    ∏ g : ι,∏ i ∈ sourceSmallShared J ell g,v g (sigma g i)
  let hit := fun O : choices => ∃ j : Σ g : G,Fin (sizes g),
    ¬ (prime j.1 j.2).val ∣ DS O*DB ∧
      r j+((o*k*(DS O*DB:ℕ):ℤ):ZMod (prime j.1 j.2).val)=0
  have hD (sigma : ι → Equiv.Perm (Fin (J+ell))) :
      DS (sourceOriginalMemoryOmissionTuple434 J ell sigma)=Ds sigma :=
    source_original_memory_omission_complement_product434 J ell v sigma
  have hMean :
      (∑ sigma : ι → Equiv.Perm (Fin (J+ell)),
        if hit (sourceOriginalMemoryOmissionTuple434 J ell sigma) then (1:ℝ) else 0) /
          (((J+ell).factorial:ℝ)^(Fintype.card ι)) =
      (∑ O : choices,if hit O then (1:ℝ) else 0) /
          (((J+ell).choose ell:ℝ)^(Fintype.card ι)) := by
    convert source_original_memory_omission_permutation_average434 J ell
      (fun O : choices => if hit O then (1:ℝ) else 0) using 1 <;> congr <;> exact Subsingleton.elim _ _
  have hCount : ((Finset.univ : Finset choices).filter hit).card ≤ ∑ g : G,sizes g :=
    hCountEvent x Y Hprime data sep (J+ell) xs hSmallUpper hBigLower
      sizes prime r DB o k ho hk0 hk
  have hsum : (∑ O : choices,if hit O then (1:ℝ) else 0) =
      (((Finset.univ : Finset choices).filter hit).card:ℝ) := by
    rw [← Finset.sum_filter]
    simp only [Finset.sum_const,nsmul_eq_mul,mul_one]
  rw [hsum] at hMean
  dsimp only [hit] at hMean
  simp_rw [hD] at hMean
  change (∑ sigma : ι → Equiv.Perm (Fin (J+ell)),
    if ∃ j : Σ g : G,Fin (sizes g),
      ¬ (prime j.1 j.2).val ∣ Ds sigma*DB ∧
        r j+((o*k*(Ds sigma*DB:ℕ):ℤ):ZMod (prime j.1 j.2).val)=0
    then (1:ℝ) else 0) / _ ≤ _
  rw [hMean]
  exact div_le_div_of_nonneg_right (by exact_mod_cast hCount)
    (pow_nonneg (Nat.cast_nonneg _) _)
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalMemoryPhysicalPromotion -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 6000000

section LiteralHit
variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ) [∀ g p,NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bigMod g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)

/-- A literal promotable OLD index at the actual original divisor and
step. This retains the nondivisibility test, orientation and mode. -/
def sourceOriginalMemoryPhysicalPromotionHit434
    (pat : SourcePattern BG J m) (aux : SourceBigAux BP J m pat)
    (st : FullPhysicalState SP smallMod BP bigMod (J+ell) cap)
    (bigSigma : BigGroupPerm (BG:=BG) (J+ell))
    (smallSigma : Green64SmallHaar.GroupPermFamily (G:=SG) (J+ell))
    (o k : ℤ) : Prop :=
  let D := sourceOrientedPhysicalD SP smallMod BP bigMod J ell m cap
    pat aux st bigSigma smallSigma
  let step := sourceOrientedStep SP smallMod BP bigMod J ell m cap
    pat aux st bigSigma smallSigma o k
  ∃ j : Σ g : BG,Fin (st.2 g).2.1.val,
    ¬ bigMod j.1 (((st.2 j.1).2.2 j.2).1) ∣ D ∧
      ((st.2 j.1).2.2 j.2).2+
        (step:ZMod (bigMod j.1 (((st.2 j.1).2.2 j.2).1)))=0

/-- Every actual legal promoted slot witnesses the literal hit event. -/
theorem source_original_memory_legal_promotion_hit434
    {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)
    (st : FullPhysicalState SP smallMod BP bigMod (J+ell) cap)
    (o k : ℤ)
    (z : FullOrientedSourceChoice SP smallMod BP bigMod J ell m cap patterns st)
    (hz : sourceOrientedPhysicalLegal SP smallMod BP bigMod
      J ell m cap patterns st o k z)
    (g : BG) (a : ↥(((z.2.2.1.bigChoice g).2).2.1)) :
    sourceOriginalMemoryPhysicalPromotionHit434 SP smallMod BP bigMod
      J ell m cap (patterns z.1) z.2.1 st z.2.2.1.sigmaBig z.2.2.2.1 o k := by
  exact ⟨⟨g,((z.2.2.1.bigChoice g).2).2.2 a⟩,
    (hz.2.2.2.1 g).promoted_not_dividing a,(hz.2.2.2.1 g).promoted_zero a⟩
end LiteralHit

/-- The arithmetic omission estimate on the literal original physical
divisor. The threshold precedes J, both moving prime families, every
physical OLD sector, pattern, auxiliary tuple and BIG permutation. -/
theorem eventually_source_original_memory_PHYSICAL_permutation_promotion_bound434
    (cfg : SourceComparisonFixed434) (ell : ℕ) (Ck : ℝ) :
    ∀ᶠ L : ℝ in atTop,
    ∀ {ι G : Type} [Fintype ι] [DecidableEq ι] [Fintype G] [DecidableEq G]
      (x Y Hprime : ℝ) (data : SourceComparisonData434 ι G cfg x L Y Hprime)
      (sep : SourceOriginalSource03GroupSeparation434 data)
      [∀ g (p : {p : ℕ // p ∈ data.Ts g}),NeZero p.val]
      [∀ g (p : {p : ℕ // p ∈ data.Tb g}),NeZero p.val]
      (J m : ℕ) (cap : G → ℕ)
      (st : FullPhysicalState
        (fun g => {p : ℕ // p ∈ data.Ts g}) (fun _ p => p.val)
        (fun g => {p : ℕ // p ∈ data.Tb g}) (fun _ p => p.val) (J+ell) cap)
      (hSmallUpper : ∀ g,∀ p ∈ data.Ts g,(p:ℝ) ≤ Real.exp (L^cfg.bexp))
      (hBigLower : ∀ g,∀ p ∈ data.Tb g,Real.exp (L^cfg.cexp) ≤ (p:ℝ))
      (pat : SourcePattern G J m)
      (aux : SourceBigAux (fun g => {p : ℕ // p ∈ data.Tb g}) J m pat)
      (bigSigma : BigGroupPerm (BG:=G) (J+ell))
      (o k : ℤ) (ho : o=1 ∨ o= -1) (hk0 : k ≠ 0)
      (hk : (k.natAbs:ℝ) ≤ L^Ck),
    (∑ smallSigma : Green64SmallHaar.GroupPermFamily (G:=ι) (J+ell),
      if sourceOriginalMemoryPhysicalPromotionHit434
        (fun g => {p : ℕ // p ∈ data.Ts g}) (fun _ p => p.val)
        (fun g => {p : ℕ // p ∈ data.Tb g}) (fun _ p => p.val)
        J ell m cap pat aux st bigSigma smallSigma o k then (1:ℝ) else 0) /
        (((J+ell).factorial:ℝ)^(Fintype.card ι)) ≤
      ((∑ g : G,(st.2 g).2.1.val:ℕ):ℝ) /
        (((J+ell).choose ell:ℝ)^(Fintype.card ι)) := by
  filter_upwards [eventually_source_original_memory_literal_permutation_promotion_bound434
    cfg ell Ck] with L hh
  intro ι G instI instDI instG instDG x Y Hprime data sep instS instB
    J m cap st hSmallUpper hBigLower pat aux bigSigma o k ho hk0 hk
  let DB : ℕ := ∏ g : G,
    (∏ i ∈ sourceBigShared J ell m pat g,((st.2 g).1 (bigSigma g i)).val) *
    (∏ j : ↥(pat.free g),(aux g j).val)
  simpa only [sourceOriginalMemoryPhysicalPromotionHit434,sourceOrientedStep,
    sourceOrientedPhysicalD,DB] using
    hh x Y Hprime data sep J st.1 hSmallUpper hBigLower
    (fun g => (st.2 g).2.1.val) (fun g i => ((st.2 g).2.2 i).1)
    (fun j => ((st.2 j.1).2.2 j.2).2) DB o k ho hk0 hk
end Green64Analytic.CorrelationSquare

end

end

