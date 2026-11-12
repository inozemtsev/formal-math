module

public import Mathlib.Data.Finset.Basic
public import Mathlib.Tactic
public import Mathlib.Data.Nat.Find
public import Mathlib.Data.Fintype.Basic
public import Green64.Library.Weights.Part022
public import Green64.Library.Weights.Part002
public import Green64.Library.Correlation.Part001
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

@[expose] public section

/-!
# Weights / Part024

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceSetLifespans -/

section

open scoped BigOperators
open Classical
namespace Green64OrderedLift

theorem source_set_lifespans :
∀ {P : Type} [Fintype P] [DecidableEq P] (T : ℕ)
 (A M F G E S K R U : ℕ → Finset P),
 U 0 = ∅ → M 0 = ∅ → F 0 = A 0 →
 (∀ i, F i ⊆ A i ∧ Disjoint (F i) (U i) ∧ Disjoint (G i) (U i ∪ F i) ∧
   E i ⊆ M i ∧ S i ⊆ A i ∧ K i ⊆ A i \ S i ∧ R i ⊆ (M i \ E i) ∪ G i ∧
   A (i+1) = S i ∪ R i ∪ F (i+1) ∧
   M (i+1) = (((M i \ E i) ∪ G i) \ R i) ∪ K i ∧
   U (i+1) = (U i ∪ F i) ∪ G i) →
 (∀ i, T ≤ i → A i = ∅ ∧ M i = ∅ ∧ F i = ∅ ∧ G i = ∅ ∧ U i = U T) →
 ∃ life : P → Option (ℕ × ℕ), ∀ p,
   match life p with
   | none => ∀ i, p ∉ A i ∧ p ∉ M i ∧ p ∉ G i
   | some az => az.1 ≤ az.2 ∧ az.2 < T ∧ (az.1 = az.2 → p ∈ A az.1) ∧ ∀ i,
       (p ∈ A i → az.1 ≤ i ∧ i ≤ az.2) ∧
       (p ∈ M i ↔ az.1 < i ∧ i ≤ az.2 ∧ p ∉ A i) ∧
       (p ∈ (M i \ E i) ∪ G i ↔ az.1 ≤ i ∧ i < az.2 ∧ p ∉ A i) ∧
       (p ∈ F i ∪ G i ↔ az.1 = i) ∧
       (p ∈ E i ∪ (A i \ (S i ∪ K i)) ↔ az.2 = i) :=
by
  have conserve : ∀ {P : Type} [DecidableEq P] (A M F G E S T R H : Finset P),
 F ⊆ A → Disjoint A M → Disjoint G (A ∪ M) →
 E ⊆ M → S ⊆ A → T ⊆ A \ S → R ⊆ (M \ E) ∪ G →
 Disjoint H (A ∪ M ∪ G) →
 let C := (M \ E) ∪ G;
 let Anext := S ∪ R ∪ H;
 let Mnext := (C \ R) ∪ T;
 let births := F ∪ G;
 let deaths := E ∪ (A \ (S ∪ T));
 let present := (A \ F ∪ M) ∪ births;
 present \ deaths = (Anext \ H) ∪ Mnext ∧
 Disjoint Anext Mnext ∧ deaths ⊆ present ∧
 births ∩ deaths ⊆ A := by
    classical
    intro P _ A M F G E S T R H hFA hAM hGAM hEM hSA hT hR hH
    dsimp only
    have rules (p : P) :
        (p ∈ F → p ∈ A) ∧
        (p ∈ A → p ∉ M) ∧
        (p ∈ G → p ∉ A ∧ p ∉ M) ∧
        (p ∈ E → p ∈ M) ∧
        (p ∈ S → p ∈ A) ∧
        (p ∈ T → p ∈ A ∧ p ∉ S) ∧
        (p ∈ R → (p ∈ M ∧ p ∉ E) ∨ p ∈ G) ∧
        (p ∈ H → p ∉ A ∧ p ∉ M ∧ p ∉ G) := by
      refine ⟨fun hp => hFA hp, fun hp => Finset.disjoint_left.mp hAM hp, ?_,
        fun hp => hEM hp, fun hp => hSA hp, ?_, ?_, ?_⟩
      · intro hp
        have hh := Finset.disjoint_left.mp hGAM hp
        exact ⟨fun h => hh (Finset.mem_union_left _ h), fun h => hh (Finset.mem_union_right _ h)⟩
      · intro hp
        exact Finset.mem_sdiff.mp (hT hp)
      · intro hp
        simpa only [Finset.mem_union,Finset.mem_sdiff] using hR hp
      · intro hp
        have hh := Finset.disjoint_left.mp hH hp
        exact ⟨fun h => hh (Finset.mem_union_left _ (Finset.mem_union_left _ h)),
          fun h => hh (Finset.mem_union_left _ (Finset.mem_union_right _ h)),
          fun h => hh (Finset.mem_union_right _ h)⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · ext p
      have hr := rules p
      simp only [Finset.mem_union, Finset.mem_sdiff]
      rcases hr with ⟨h1,h2,h3,h4,h5,h6,h7,h8⟩
      clear rules hFA hAM hGAM hEM hSA hT hR hH
      grind
    · apply Finset.disjoint_left.mpr
      intro p hp hq
      have hr := rules p
      simp only [Finset.mem_union, Finset.mem_sdiff] at hp hq
      rcases hr with ⟨h1,h2,h3,h4,h5,h6,h7,h8⟩
      clear rules hFA hAM hGAM hEM hSA hT hR hH
      grind
    · intro p hp
      have hr := rules p
      simp only [Finset.mem_union, Finset.mem_sdiff] at hp ⊢
      rcases hr with ⟨h1,h2,h3,h4,h5,h6,h7,h8⟩
      clear rules hFA hAM hGAM hEM hSA hT hR hH
      grind
    · intro p hp
      have hr := rules p
      simp only [Finset.mem_inter, Finset.mem_union, Finset.mem_sdiff] at hp
      rcases hr with ⟨h1,h2,h3,h4,h5,h6,h7,h8⟩
      clear rules hFA hAM hGAM hEM hSA hT hR hH
      grind
  have extractLife : ∀ {P : Type} [Fintype P] [DecidableEq P] (T : ℕ)
 (U L B D : ℕ → Finset P),
 U 0 = ∅ → L 0 = ∅ →
 (∀ i, D i ⊆ L i ∪ B i ∧ Disjoint (B i) (U i) ∧
   U (i+1) = U i ∪ B i ∧ L (i+1) = (L i ∪ B i) \ D i) →
 L T = ∅ →
 (∀ i, T ≤ i → U i = U T ∧ L i = L T ∧ B i = ∅) →
 ∃ life : P → Option (ℕ × ℕ), ∀ p,
   match life p with
   | none => ∀ i, p ∉ L i ∪ B i ∧ p ∉ B i ∧ p ∉ D i
   | some az => az.1 ≤ az.2 ∧ az.2 < T ∧ ∀ i,
       (p ∈ L i ∪ B i ↔ az.1 ≤ i ∧ i ≤ az.2) ∧
       (p ∈ B i ↔ az.1 = i) ∧ (p ∈ D i ↔ az.2 = i) := by
    clear conserve
    have refineClock : ∀ {P : Type} [Fintype P] [DecidableEq P] (T : ℕ)
   (U L B D : ℕ → Finset P),
   U 0 = ∅ → L 0 = ∅ →
   (∀ i, D i ⊆ L i ∪ B i ∧ Disjoint (B i) (U i) ∧
     U (i+1) = U i ∪ B i ∧ L (i+1) = (L i ∪ B i) \ D i) →
   L T = ∅ →
   (∀ i, T ≤ i → U i = U T ∧ L i = L T ∧ B i = ∅) →
   let Span := {bd : ℕ × ℕ // 0 < bd.1 ∧ bd.1 < bd.2 ∧ bd.2 ≤ 2*T};
   let encode (s : Option Span) (i : ℕ) : ℕ :=
     match s with
     | none => 0
     | some bd => if i < bd.val.1 then 0 else if i < bd.val.2 then 1 else 2;
   ∃ s : P → Option Span, (∀ i p,
     (p ∈ L i ∪ B i ↔ encode (s p) (2*i+1) = 1) ∧
     (p ∈ B i ↔ encode (s p) (2*i) = 0 ∧ encode (s p) (2*i+1) = 1) ∧
     (p ∈ D i ↔ encode (s p) (2*i+1) = 1 ∧ encode (s p) (2*i+2) = 2)) ∧
     ∀ p (bd : Span), s p = some bd → bd.val.1 % 2 = 1 ∧ bd.val.2 % 2 = 0 := by
      have flow : ∀ {P : Type} [Fintype P] [DecidableEq P] (T : ℕ),
     let Span := {bd : ℕ × ℕ // 0 < bd.1 ∧ bd.1 < bd.2 ∧ bd.2 ≤ T};
     let encode (s : Option Span) (i : ℕ) : ℕ :=
       match s with
       | none => 0
       | some bd => if i < bd.val.1 then 0 else if i < bd.val.2 then 1 else 2;
     let Data := (ℕ → Finset P) × (ℕ → Finset P) × (ℕ → Finset P) × (ℕ → Finset P);
     let validFlow (x : Data) : Prop :=
       x.1 0 = ∅ ∧ x.2.1 0 = ∅ ∧
       (∀ i, x.2.2.2 i ⊆ x.2.1 i ∧ Disjoint (x.2.2.1 i) (x.1 i) ∧
         x.1 (i+1) = x.1 i ∪ x.2.2.1 i ∧
         x.2.1 (i+1) = (x.2.1 i \ x.2.2.2 i) ∪ x.2.2.1 i) ∧
       x.2.1 T = ∅ ∧ (∀ i, T ≤ i → x.1 i = x.1 T ∧ x.2.1 i = x.2.1 T);
     ∃ e : (P → Option Span) ≃ {x : Data // validFlow x},
       ∀ s i p,
         (p ∈ (e s).val.1 i ↔ encode (s p) i ≠ 0) ∧
         (p ∈ (e s).val.2.1 i ↔ encode (s p) i = 1) ∧
         (p ∈ (e s).val.2.2.1 i ↔ encode (s p) i = 0 ∧ encode (s p) (i+1) = 1) ∧
         (p ∈ (e s).val.2.2.2 i ↔ encode (s p) i = 1 ∧ encode (s p) (i+1) = 2) := by
        have phaseOfEvent : ∀ {P : Type} [Fintype P] [DecidableEq P] (T : ℕ)
       (U L B D : ℕ → Finset P),
       U 0 = ∅ → L 0 = ∅ →
       (∀ i, D i ⊆ L i ∧ Disjoint (B i) (U i) ∧
         U (i+1) = U i ∪ B i ∧ L (i+1) = (L i \ D i) ∪ B i) →
       L T = ∅ →
       (∀ i, T ≤ i → U i = U T ∧ L i = L T) →
       let phase (p : P) (i : ℕ) := if p ∈ L i then 1 else if p ∈ U i then 2 else 0;
       (∀ i, L i ⊆ U i) ∧
       (∀ p, phase p 0 = 0 ∧
         (∀ i, phase p i ≤ phase p (i+1) ∧ phase p (i+1) ≤ phase p i + 1) ∧
         (∀ i, phase p i ≤ 2) ∧ phase p T ≠ 1 ∧
         (∀ i, T ≤ i → phase p i = phase p T)) ∧
       (∀ i p, (p ∈ U i ↔ phase p i ≠ 0) ∧ (p ∈ L i ↔ phase p i = 1) ∧
         (p ∈ B i ↔ phase p i = 0 ∧ phase p (i+1) = 1) ∧
         (p ∈ D i ↔ phase p i = 1 ∧ phase p (i+1) = 2)) := by
          classical
          intro P _ _ T U L B D hU0 hL0 step hLT tail
          dsimp only
          let phase (p : P) (i : ℕ) := if p ∈ L i then 1 else if p ∈ U i then 2 else 0
          have sub : ∀ i, L i ⊆ U i := by
            intro i
            induction i with
            | zero => simp [hU0,hL0]
            | succ i ih =>
              intro p hp
              rw [(step i).2.2.2] at hp
              rw [(step i).2.2.1]
              rcases Finset.mem_union.mp hp with hp|hp
              · exact Finset.mem_union_left _ (ih (Finset.mem_sdiff.mp hp).1)
              · exact Finset.mem_union_right _ hp
          have one (i : ℕ) (p : P) :
              phase p i ≤ phase p (i+1) ∧ phase p (i+1) ≤ phase p i + 1 ∧
              (p ∈ B i ↔ phase p i = 0 ∧ phase p (i+1) = 1) ∧
              (p ∈ D i ↔ phase p i = 1 ∧ phase p (i+1) = 2) := by
            have hd : p ∈ D i → p ∈ L i := fun h => (step i).1 h
            have hf : p ∈ B i → p ∉ U i := fun h => Finset.disjoint_left.mp (step i).2.1 h
            have hu : p ∈ U (i+1) ↔ p ∈ U i ∨ p ∈ B i := by rw [(step i).2.2.1]; simp
            have hl : p ∈ L (i+1) ↔ (p ∈ L i ∧ p ∉ D i) ∨ p ∈ B i := by
              rw [(step i).2.2.2]; simp
            have hsub : p ∈ L i → p ∈ U i := fun h => sub i h
            try dsimp [phase]
            by_cases h1 : p ∈ L i <;> by_cases h2 : p ∈ U i <;>
              by_cases h3 : p ∈ B i <;> by_cases h4 : p ∈ D i <;>
              simp_all
          refine ⟨sub, ?_, ?_⟩
          · intro p
            refine ⟨?_, ?_, ?_, ?_, ?_⟩
            · simp [phase, hU0, hL0]
            · intro i
              exact ⟨(one i p).1, (one i p).2.1⟩
            · intro i
              try dsimp [phase]
              split_ifs <;> omega
            · simp [hLT]
              split_ifs <;> norm_num
            · intro i hi
              rw [(tail i hi).1, (tail i hi).2]
          · intro i p
            refine ⟨?_, ?_, (one i p).2.2.1, (one i p).2.2.2⟩
            · have hh : p ∈ L i → p ∈ U i := fun h => sub i h
              try dsimp [phase]
              split_ifs <;> simp_all
            · try dsimp [phase]
              split_ifs <;> simp_all
        have eventOfPhase : ∀ {P : Type} [Fintype P] [DecidableEq P] (T : ℕ)
       (f : P → ℕ → ℕ),
       (∀ p, f p 0 = 0 ∧
         (∀ i, f p i ≤ f p (i+1) ∧ f p (i+1) ≤ f p i + 1) ∧
         (∀ i, f p i ≤ 2) ∧ f p T ≠ 1 ∧ (∀ i, T ≤ i → f p i = f p T)) →
       let U (i : ℕ) := Finset.univ.filter (fun p => f p i ≠ 0);
       let L (i : ℕ) := Finset.univ.filter (fun p => f p i = 1);
       let B (i : ℕ) := Finset.univ.filter (fun p => f p i = 0 ∧ f p (i+1) = 1);
       let D (i : ℕ) := Finset.univ.filter (fun p => f p i = 1 ∧ f p (i+1) = 2);
       U 0 = ∅ ∧ L 0 = ∅ ∧
       (∀ i, D i ⊆ L i ∧ Disjoint (B i) (U i) ∧
         U (i+1) = U i ∪ B i ∧ L (i+1) = (L i \ D i) ∪ B i) ∧
       L T = ∅ ∧ (∀ i, T ≤ i → U i = U T ∧ L i = L T) ∧
       (∀ p i, (if p ∈ L i then 1 else if p ∈ U i then 2 else 0) = f p i) := by
          classical
          intro P _ _ T f hf
          dsimp only
          let U (i : ℕ) := Finset.univ.filter (fun p => f p i ≠ 0)
          let L (i : ℕ) := Finset.univ.filter (fun p => f p i = 1)
          let B (i : ℕ) := Finset.univ.filter (fun p => f p i = 0 ∧ f p (i+1) = 1)
          let D (i : ℕ) := Finset.univ.filter (fun p => f p i = 1 ∧ f p (i+1) = 2)
          change U 0 = ∅ ∧ L 0 = ∅ ∧
            (∀ i, D i ⊆ L i ∧ Disjoint (B i) (U i) ∧
              U (i+1) = U i ∪ B i ∧ L (i+1) = (L i \ D i) ∪ B i) ∧
            L T = ∅ ∧ (∀ i, T ≤ i → U i = U T ∧ L i = L T) ∧
            (∀ p i, (if p ∈ L i then 1 else if p ∈ U i then 2 else 0) = f p i)
          refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
          · ext p
            simp [U, (hf p).1]
          · ext p
            simp [L, (hf p).1]
          · intro i
            refine ⟨?_, ?_, ?_, ?_⟩
            · intro p hp
              simp only [D,L,Finset.mem_filter,Finset.mem_univ,true_and] at *
              exact hp.1
            · apply Finset.disjoint_left.mpr
              intro p hp hq
              simp only [B,U,Finset.mem_filter,Finset.mem_univ,true_and] at *
              exact hq hp.1
            · ext p
              simp only [U,B,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_union]
              have hstep := (hf p).2.1 i
              omega
            · ext p
              simp only [L,B,D,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_union,Finset.mem_sdiff]
              have hstep := (hf p).2.1 i
              have hbi := (hf p).2.2.1 i
              have hbn := (hf p).2.2.1 (i+1)
              omega
          · ext p
            simp [L, (hf p).2.2.2.1]
          · intro i hi
            constructor <;> ext p <;>
              simp [U,L, (hf p).2.2.2.2 i hi]
          · intro p i
            simp only [L,U,Finset.mem_filter,Finset.mem_univ,true_and]
            have hb := (hf p).2.2.1 i
            split_ifs <;> omega
        have simultaneous : ∀ (P : Type) (T : ℕ),
       let Span := {bd : ℕ × ℕ // 0 < bd.1 ∧ bd.1 < bd.2 ∧ bd.2 ≤ T};
       let valid (f : ℕ → ℕ) : Prop :=
         f 0 = 0 ∧ (∀ i, f i ≤ f (i+1) ∧ f (i+1) ≤ f i + 1) ∧
         (∀ i, f i ≤ 2) ∧ f T ≠ 1 ∧ (∀ i, T ≤ i → f i = f T);
       let encode (s : Option Span) (i : ℕ) : ℕ :=
         match s with
         | none => 0
         | some bd => if i < bd.val.1 then 0 else if i < bd.val.2 then 1 else 2;
       ∃ e : (P → Option Span) ≃ {f : P → ℕ → ℕ // ∀ p, valid (f p)},
         ∀ s p i, (e s).val p i = encode (s p) i := by
          have scalar : ∀ (T : ℕ),
         let Span := {bd : ℕ × ℕ // 0 < bd.1 ∧ bd.1 < bd.2 ∧ bd.2 ≤ T};
         let valid (f : ℕ → ℕ) : Prop :=
           f 0 = 0 ∧ (∀ i, f i ≤ f (i+1) ∧ f (i+1) ≤ f i + 1) ∧
           (∀ i, f i ≤ 2) ∧ f T ≠ 1 ∧ (∀ i, T ≤ i → f i = f T);
         let encode (s : Option Span) (i : ℕ) : ℕ :=
           match s with
           | none => 0
           | some bd => if i < bd.val.1 then 0 else if i < bd.val.2 then 1 else 2;
         (∀ s, valid (encode s)) ∧
         (∀ f, valid f → ∃! s, encode s = f) := by
            have interval : ∀ (T : ℕ) (f : ℕ → ℕ),
           f 0 = 0 →
           (∀ i, f i ≤ f (i+1) ∧ f (i+1) ≤ f i + 1) →
           (∀ i, f i ≤ 2) →
           f T = 2 →
           ∃ b d : ℕ, 0 < b ∧ b < d ∧ d ≤ T ∧
             (∀ i, f i = if i < b then 0 else if i < d then 1 else 2) ∧
             (∀ b' d', 0 < b' → b' < d' → d' ≤ T →
               (∀ i, f i = if i < b' then 0 else if i < d' then 1 else 2) →
                 b' = b ∧ d' = d) := by
              intro T f h0 hs hb hT
              have mono : Monotone f := monotone_nat_of_le_succ (fun i => (hs i).1)
              have exb : ∃ i, 1 ≤ f i := ⟨T, by omega⟩
              have exd : ∃ i, 2 ≤ f i := ⟨T, by omega⟩
              let b := Nat.find exb
              let d := Nat.find exd
              have fb : 1 ≤ f b := Nat.find_spec exb
              have fd : 2 ≤ f d := Nat.find_spec exd
              have db : d ≤ T := Nat.find_min' exd (by omega)
              have bpos : 0 < b := by
                by_contra h
                have : b = 0 := by omega
                rw [this, h0] at fb
                omega
              have pre_b : ∀ i, i < b → f i = 0 := by
                intro i hi
                have : ¬ 1 ≤ f i := Nat.find_min exb hi
                omega
              have pre_d : ∀ i, i < d → f i ≤ 1 := by
                intro i hi
                have : ¬ 2 ≤ f i := Nat.find_min exd hi
                omega
              have fb1 : f b = 1 := by
                have hprev := pre_b (b-1) (by omega)
                have hstep := (hs (b-1)).2
                have he : b-1+1 = b := by omega
                rw [he, hprev] at hstep
                omega
              have bd : b < d := by
                by_contra h
                have hmono := mono (show d ≤ b by omega)
                omega
              have shape : ∀ i, f i = if i < b then 0 else if i < d then 1 else 2 := by
                intro i
                by_cases hi : i < b
                · simp [hi, pre_b i hi]
                · by_cases hd : i < d
                  · have hmono := mono (show b ≤ i by omega)
                    have hupper := pre_d i hd
                    simp only [hi, hd, if_false, if_true]
                    omega
                  · have hmono := mono (show d ≤ i by omega)
                    have hupper := hb i
                    simp only [hi, hd, if_false]
                    omega
              refine ⟨b, d, bpos, bd, db, shape, ?_⟩
              intro b' d' hb' hbd' hd' shape'
              have bb : b' = b := by
                have h1 := shape b
                have h2 := shape' b
                have h3 := shape b'
                have h4 := shape' b'
                split_ifs at h1 h2 h3 h4 <;> omega
              subst b'
              have dd : d' = d := by
                have h1 := shape d
                have h2 := shape' d
                have h3 := shape d'
                have h4 := shape' d'
                split_ifs at h1 h2 h3 h4 <;> omega
              exact ⟨rfl, dd⟩
            intro T
            dsimp only
            let Span := {bd : ℕ × ℕ // 0 < bd.1 ∧ bd.1 < bd.2 ∧ bd.2 ≤ T}
            let valid (f : ℕ → ℕ) : Prop :=
              f 0 = 0 ∧ (∀ i, f i ≤ f (i+1) ∧ f (i+1) ≤ f i + 1) ∧
              (∀ i, f i ≤ 2) ∧ f T ≠ 1 ∧ (∀ i, T ≤ i → f i = f T)
            let encode (s : Option Span) (i : ℕ) : ℕ :=
              match s with
              | none => 0
              | some bd => if i < bd.val.1 then 0 else if i < bd.val.2 then 1 else 2
            change (∀ s, valid (encode s)) ∧ (∀ f, valid f → ∃! s, encode s = f)
            have encvalid : ∀ s, valid (encode s) := by
              intro s
              cases s with
              | none => simp [valid, encode]
              | some bd =>
                rcases bd with ⟨⟨b,d⟩, hb, hbd, hd⟩
                dsimp [valid, encode]
                refine ⟨?_, ?_, ?_, ?_, ?_⟩
                · simp [hb]
                · intro i
                  split_ifs <;> omega
                · intro i
                  split_ifs <;> omega
                · split_ifs <;> omega
                · intro i hi
                  split_ifs <;> omega
            refine ⟨encvalid, ?_⟩
            intro f hf
            rcases hf with ⟨h0, hs, hb, hv, htail⟩
            have mono : Monotone f := monotone_nat_of_le_succ (fun i => (hs i).1)
            by_cases ht : f T = 0
            · have hfzero : f = fun _ => 0 := by
                funext i
                by_cases hi : i ≤ T
                · have := mono hi
                  omega
                · rw [htail i (by omega), ht]
              refine ⟨none, ?_, ?_⟩
              · exact hfzero.symm
              · intro s he
                cases s with
                | none => rfl
                | some bd =>
                  have ee := congrFun he bd.val.1
                  have hh := congrFun hfzero bd.val.1
                  have hbd := bd.property.2.1
                  simp [encode, hbd] at ee
                  omega
            · have ht2 : f T = 2 := by have := hb T; omega
              obtain ⟨b,d,hbp,hbd,hd,shape,uniq⟩ := interval T f h0 hs hb ht2
              let bd : Span := ⟨(b,d),hbp,hbd,hd⟩
              refine ⟨some bd, ?_, ?_⟩
              · funext i
                exact (shape i).symm
              · intro s he
                cases s with
                | none =>
                  have ee := congrFun he T
                  change 0 = f T at ee
                  omega
                | some bd' =>
                  have shp : ∀ i, f i = if i < bd'.val.1 then 0 else if i < bd'.val.2 then 1 else 2 := by
                    intro i
                    exact (congrFun he i).symm
                  obtain ⟨e1,e2⟩ := uniq bd'.val.1 bd'.val.2 bd'.property.1 bd'.property.2.1 bd'.property.2.2 shp
                  congr 1
                  apply Subtype.ext
                  exact Prod.ext e1 e2
          classical
          intro P T
          dsimp only
          let Span := {bd : ℕ × ℕ // 0 < bd.1 ∧ bd.1 < bd.2 ∧ bd.2 ≤ T}
          let valid (f : ℕ → ℕ) : Prop :=
            f 0 = 0 ∧ (∀ i, f i ≤ f (i+1) ∧ f (i+1) ≤ f i + 1) ∧
            (∀ i, f i ≤ 2) ∧ f T ≠ 1 ∧ (∀ i, T ≤ i → f i = f T)
          let encode (s : Option Span) (i : ℕ) : ℕ :=
            match s with
            | none => 0
            | some bd => if i < bd.val.1 then 0 else if i < bd.val.2 then 1 else 2
          let Tr := {f : P → ℕ → ℕ // ∀ p, valid (f p)}
          have hscalar : (∀ s, valid (encode s)) ∧ (∀ f, valid f → ∃! s, encode s = f) := scalar T
          let forward (s : P → Option Span) : Tr :=
            ⟨fun p => encode (s p), fun p => hscalar.1 (s p)⟩
          have hi : Function.Injective forward := by
            intro s t h
            funext p
            have hs := hscalar.2 (encode (s p)) (hscalar.1 (s p))
            obtain ⟨u,hu,huniq⟩ := hs
            have hst : encode (t p) = encode (s p) := by
              exact (congrFun (congrArg Subtype.val h) p).symm
            exact (huniq (s p) rfl).trans (huniq (t p) hst).symm
          have hs : Function.Surjective forward := by
            intro f
            choose s h using fun p => (hscalar.2 (f.val p) (f.property p)).exists
            refine ⟨s, ?_⟩
            apply Subtype.ext
            funext p
            exact h p
          refine ⟨Equiv.ofBijective forward ⟨hi,hs⟩, ?_⟩
          intro s p i
          rfl
        classical
        intro P _ _ T
        dsimp only
        let Span := {bd : ℕ × ℕ // 0 < bd.1 ∧ bd.1 < bd.2 ∧ bd.2 ≤ T}
        let encode (s : Option Span) (i : ℕ) : ℕ :=
          match s with
          | none => 0
          | some bd => if i < bd.val.1 then 0 else if i < bd.val.2 then 1 else 2
        let valid (f : ℕ → ℕ) : Prop :=
          f 0 = 0 ∧ (∀ i, f i ≤ f (i+1) ∧ f (i+1) ≤ f i + 1) ∧
          (∀ i, f i ≤ 2) ∧ f T ≠ 1 ∧ (∀ i, T ≤ i → f i = f T)
        let Trace := {f : P → ℕ → ℕ // ∀ p, valid (f p)}
        let Data := (ℕ → Finset P) × (ℕ → Finset P) × (ℕ → Finset P) × (ℕ → Finset P)
        let validFlow (x : Data) : Prop :=
          x.1 0 = ∅ ∧ x.2.1 0 = ∅ ∧
          (∀ i, x.2.2.2 i ⊆ x.2.1 i ∧ Disjoint (x.2.2.1 i) (x.1 i) ∧
            x.1 (i+1) = x.1 i ∪ x.2.2.1 i ∧
            x.2.1 (i+1) = (x.2.1 i \ x.2.2.2 i) ∪ x.2.2.1 i) ∧
          x.2.1 T = ∅ ∧ (∀ i, T ≤ i → x.1 i = x.1 T ∧ x.2.1 i = x.2.1 T)
        let Flow := {x : Data // validFlow x}
        let toFlow (f : Trace) : Flow :=
          ⟨(fun i => Finset.univ.filter (fun p => f.val p i ≠ 0),
            fun i => Finset.univ.filter (fun p => f.val p i = 1),
            fun i => Finset.univ.filter (fun p => f.val p i = 0 ∧ f.val p (i+1) = 1),
            fun i => Finset.univ.filter (fun p => f.val p i = 1 ∧ f.val p (i+1) = 2)), by
              have h := eventOfPhase T f.val f.property
              exact ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2.1⟩⟩
        let toTrace (x : Flow) : Trace :=
          ⟨fun p i => if p ∈ x.val.2.1 i then 1 else if p ∈ x.val.1 i then 2 else 0, by
            have h := phaseOfEvent T x.val.1 x.val.2.1 x.val.2.2.1 x.val.2.2.2
              x.property.1 x.property.2.1 x.property.2.2.1 x.property.2.2.2.1 x.property.2.2.2.2
            exact h.2.1⟩
        have left : ∀ f, toTrace (toFlow f) = f := by
          intro f
          apply Subtype.ext
          funext p i
          exact (eventOfPhase T f.val f.property).2.2.2.2.2 p i
        have right : ∀ x, toFlow (toTrace x) = x := by
          intro x
          have h := (phaseOfEvent T x.val.1 x.val.2.1 x.val.2.2.1 x.val.2.2.2
            x.property.1 x.property.2.1 x.property.2.2.1 x.property.2.2.2.1 x.property.2.2.2.2).2.2
          apply Subtype.ext
          apply Prod.ext
          · funext i
            ext p
            simpa only [toFlow, toTrace, Finset.mem_filter, Finset.mem_univ, true_and] using (h i p).1.symm
          · apply Prod.ext
            · funext i
              ext p
              simpa only [toFlow, toTrace, Finset.mem_filter, Finset.mem_univ, true_and] using (h i p).2.1.symm
            · apply Prod.ext
              · funext i
                ext p
                simpa only [toFlow, toTrace, Finset.mem_filter, Finset.mem_univ, true_and] using (h i p).2.2.1.symm
              · funext i
                ext p
                simpa only [toFlow, toTrace, Finset.mem_filter, Finset.mem_univ, true_and] using (h i p).2.2.2.symm
        let tf : Trace ≃ Flow := {toFun := toFlow, invFun := toTrace, left_inv := left, right_inv := right}
        obtain ⟨st,hst⟩ := simultaneous P T
        refine ⟨st.trans tf, ?_⟩
        intro s i p
        change (p ∈ (toFlow (st s)).val.1 i ↔ encode (s p) i ≠ 0) ∧
          (p ∈ (toFlow (st s)).val.2.1 i ↔ encode (s p) i = 1) ∧
          (p ∈ (toFlow (st s)).val.2.2.1 i ↔ encode (s p) i = 0 ∧ encode (s p) (i+1) = 1) ∧
          (p ∈ (toFlow (st s)).val.2.2.2 i ↔ encode (s p) i = 1 ∧ encode (s p) (i+1) = 2)
        simp [toFlow, hst, encode]
        exact ⟨Iff.rfl, Iff.rfl, Iff.rfl, Iff.rfl⟩
      classical
      intro P _ _ T U L B D hU hL hlocal hLT htail
      dsimp only
      let UU (i : ℕ) := if i%2=0 then U (i/2) else U (i/2) ∪ B (i/2)
      let LL (i : ℕ) := if i%2=0 then L (i/2) else L (i/2) ∪ B (i/2)
      let BB (i : ℕ) := if i%2=0 then B (i/2) else ∅
      let DD (i : ℕ) := if i%2=0 then ∅ else D (i/2)
      have even (i : ℕ) :
          UU (2*i) = U i ∧ LL (2*i) = L i ∧ BB (2*i) = B i ∧ DD (2*i) = ∅ := by
        simp [UU, LL, BB, DD]
      have odd (i : ℕ) :
          UU (2*i+1) = U i ∪ B i ∧ LL (2*i+1) = L i ∪ B i ∧
          BB (2*i+1) = ∅ ∧ DD (2*i+1) = D i := by
        have hd : (2*i+1)/2=i := by omega
        have hm : (2*i+1)%2=1 := by omega
        simp [UU, LL, BB, DD, hd, hm]
      have hstep (i : ℕ) : DD i ⊆ LL i ∧ Disjoint (BB i) (UU i) ∧
          UU (i+1) = UU i ∪ BB i ∧ LL (i+1) = (LL i \ DD i) ∪ BB i := by
        by_cases hi : i%2=0
        · obtain ⟨j,rfl⟩ : ∃ j, i=2*j := ⟨i/2,by omega⟩
          rw [(even j).1, (even j).2.1, (even j).2.2.1, (even j).2.2.2,
            (odd j).1, (odd j).2.1]
          simp [(hlocal j).2.1]
        · obtain ⟨j,rfl⟩ : ∃ j, i=2*j+1 := ⟨i/2,by omega⟩
          have he : 2*j+1+1=2*(j+1) := by omega
          rw [he, (even (j+1)).1, (even (j+1)).2.1,
            (odd j).1, (odd j).2.1, (odd j).2.2.1, (odd j).2.2.2]
          simp [(hlocal j).1, (hlocal j).2.2.1, (hlocal j).2.2.2]
      have htail' (i : ℕ) (hi : 2*T ≤ i) : UU i = UU (2*T) ∧ LL i = LL (2*T) := by
        have hj : T ≤ i/2 := by omega
        have ht := htail (i/2) hj
        rw [(even T).1, (even T).2.1]
        simp [UU, LL, ht.1, ht.2.1, ht.2.2]
      obtain ⟨e,he⟩ := flow (P:=P) (2*T)
      let x := (UU,LL,BB,DD)
      have hx : x.1 0 = ∅ ∧ x.2.1 0 = ∅ ∧
          (∀ i, x.2.2.2 i ⊆ x.2.1 i ∧ Disjoint (x.2.2.1 i) (x.1 i) ∧
            x.1 (i+1) = x.1 i ∪ x.2.2.1 i ∧
            x.2.1 (i+1) = (x.2.1 i \ x.2.2.2 i) ∪ x.2.2.1 i) ∧
          x.2.1 (2*T) = ∅ ∧
          (∀ i, 2*T ≤ i → x.1 i = x.1 (2*T) ∧ x.2.1 i = x.2.1 (2*T)) :=
        ⟨by simpa [x,UU] using hU, by simpa [x,LL] using hL, hstep,
         by change LL (2*T) = ∅; exact (even T).2.1.trans hLT, htail'⟩
      let s := e.symm ⟨x,hx⟩
      have hs : e s = ⟨x,hx⟩ := e.apply_symm_apply _
      refine ⟨s, ?_, ?_⟩
      · intro i p
        have ho := he s (2*i+1) p
        have hev := he s (2*i) p
        rw [hs] at ho hev
        change (p ∈ UU (2*i+1) ↔ _) ∧ (p ∈ LL (2*i+1) ↔ _) ∧
          (p ∈ BB (2*i+1) ↔ _) ∧ (p ∈ DD (2*i+1) ↔ _) at ho
        change (p ∈ UU (2*i) ↔ _) ∧ (p ∈ LL (2*i) ↔ _) ∧
          (p ∈ BB (2*i) ↔ _) ∧ (p ∈ DD (2*i) ↔ _) at hev
        rw [(odd i).2.1, (odd i).2.2.2] at ho
        rw [(even i).2.2.1] at hev
        exact ⟨ho.2.1,hev.2.2.1,ho.2.2.2⟩
      · intro p bd hp
        obtain ⟨hbpos,hbd,hdT⟩ := bd.property
        have hb := (he s (bd.val.1-1) p).2.2.1
        have hd := (he s (bd.val.2-1) p).2.2.2
        rw [hs] at hb hd
        have hbm : p ∈ BB (bd.val.1-1) := by
          apply hb.mpr
          simp only [hp]
          split_ifs <;> omega
        have hdm : p ∈ DD (bd.val.2-1) := by
          apply hd.mpr
          simp only [hp]
          split_ifs <;> omega
        have hbmod : (bd.val.1-1)%2=0 := by
          by_contra h
          simpa [BB,h] using hbm
        have hdmod : (bd.val.2-1)%2≠0 := by
          intro h
          simpa [DD,h] using hdm
        omega
    classical
    intro P _ _ T U L B D hU hL hlocal hLT htail
    obtain ⟨s,hs,hpar⟩ := refineClock T U L B D hU hL hlocal hLT htail
    let life (p : P) : Option (ℕ × ℕ) :=
      (s p).map (fun bd => (bd.val.1 / 2, (bd.val.2-1)/2))
    refine ⟨life, ?_⟩
    intro p
    cases hp : s p with
    | none =>
      simp only [life, hp, Option.map_none]
      intro i
      have hh := hs i p
      simpa [hp] using hh
    | some bd =>
      simp only [life, hp, Option.map_some]
      obtain ⟨hbpos,hbd,hdT⟩ := bd.property
      obtain ⟨hbmod,hdmod⟩ := hpar p bd hp
      refine ⟨by omega,by omega,?_⟩
      intro i
      have hh := hs i p
      simp only [hp] at hh
      constructor
      · rw [hh.1]
        split_ifs <;> (try simp only [false_iff, true_iff, and_false, false_and, true_and, and_true]) <;> omega
      · constructor
        · rw [hh.2.1]
          split_ifs <;> (try simp only [false_iff, true_iff, and_false, false_and, true_and, and_true]) <;> omega
        · rw [hh.2.2]
          split_ifs <;> (try simp only [false_iff, true_iff, and_false, false_and, true_and, and_true]) <;> omega
  classical
  intro P _ _ T A M F G E S K R U hU0 hM0 hF0 rows tail
  have prep (i : ℕ) (hu : A i \ F i ∪ M i ⊆ U i) :
      A i ∪ M i ∪ G i ⊆ U (i+1) ∧
      Disjoint (G i) (A i ∪ M i) ∧
      Disjoint (F (i+1)) (A i ∪ M i ∪ G i) := by
    rcases rows i with ⟨hFA,hFU,hGU,hEM,hSA,hK,hR,hAn,hMn,hUn⟩
    have hsub : A i ∪ M i ⊆ U i ∪ F i := by
      intro p hp
      rcases Finset.mem_union.mp hp with ha | hm
      · by_cases hf : p ∈ F i
        · exact Finset.mem_union_right _ hf
        · exact Finset.mem_union_left _ (hu (Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨ha,hf⟩)))
      · exact Finset.mem_union_left _ (hu (Finset.mem_union_right _ hm))
    have hAll : A i ∪ M i ∪ G i ⊆ U (i+1) := by
      rw [hUn]
      exact Finset.union_subset_union_left hsub
    refine ⟨hAll, ?_, ?_⟩
    · apply Finset.disjoint_left.mpr
      intro p hg hp
      exact Finset.disjoint_left.mp hGU hg (hsub hp)
    · apply Finset.disjoint_left.mpr
      intro p hf hp
      exact Finset.disjoint_left.mp (rows (i+1)).2.1 hf (hAll hp)
  have invariant (i : ℕ) : Disjoint (A i) (M i) ∧ A i \ F i ∪ M i ⊆ U i := by
    induction i with
    | zero => simp [hM0,hF0]
    | succ i ih =>
      rcases rows i with ⟨hFA,hFU,hGU,hEM,hSA,hK,hR,hAn,hMn,hUn⟩
      obtain ⟨hAll,hG,hH⟩ := prep i ih.2
      have hc := conserve (A i) (M i) (F i) (G i) (E i) (S i) (K i) (R i) (F (i+1))
        hFA ih.1 hG hEM hSA hK hR hH
      constructor
      · rw [hAn,hMn]
        exact hc.2.1
      · have hC : (M i \ E i) ∪ G i ⊆ U (i+1) := by
          intro p hp
          apply hAll
          rcases Finset.mem_union.mp hp with hm | hg
          · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_sdiff.mp hm).1)
          · exact Finset.mem_union_right _ hg
        have hAu : A i ⊆ U (i+1) := by
          intro p hp
          exact hAll (Finset.mem_union_left _ (Finset.mem_union_left _ hp))
        intro p hp
        rw [hAn,hMn] at hp
        simp only [Finset.mem_union,Finset.mem_sdiff] at hp
        rcases hp with ⟨hp,hn⟩ | hp
        · rcases hp with (hs | hr) | hf
          · exact hAu (hSA hs)
          · exact hC (hR hr)
          · exact False.elim (hn hf)
        · rcases hp with ⟨hp,_⟩ | hk
          · exact hC (by simpa only [Finset.mem_union,Finset.mem_sdiff] using hp)
          · exact hAu (Finset.mem_sdiff.mp (hK hk)).1
  let L (i : ℕ) := A i \ F i ∪ M i
  let B (i : ℕ) := F i ∪ G i
  let D (i : ℕ) := E i ∪ (A i \ (S i ∪ K i))
  have hcon (i : ℕ) :
      (L i ∪ B i) \ D i = L (i+1) ∧
      D i ⊆ L i ∪ B i ∧ B i ∩ D i ⊆ A i := by
    rcases rows i with ⟨hFA,hFU,hGU,hEM,hSA,hK,hR,hAn,hMn,hUn⟩
    obtain ⟨_,hG,hH⟩ := prep i (invariant i).2
    have hc := conserve (A i) (M i) (F i) (G i) (E i) (S i) (K i) (R i) (F (i+1))
      hFA (invariant i).1 hG hEM hSA hK hR hH
    refine ⟨?_,hc.2.2.1,hc.2.2.2⟩
    change _ = A (i+1) \ F (i+1) ∪ M (i+1)
    rw [hAn,hMn]
    exact hc.1
  have hlocalSource (i : ℕ) : D i ⊆ L i ∪ B i ∧ Disjoint (B i) (U i) ∧
      U (i+1) = U i ∪ B i ∧ L (i+1) = (L i ∪ B i) \ D i := by
    rcases rows i with ⟨hFA,hFU,hGU,hEM,hSA,hK,hR,hAn,hMn,hUn⟩
    refine ⟨(hcon i).2.1, ?_, ?_, (hcon i).1.symm⟩
    · apply Finset.disjoint_left.mpr
      intro p hp hu
      rcases Finset.mem_union.mp hp with hf | hg
      · exact Finset.disjoint_left.mp hFU hf hu
      · exact Finset.disjoint_left.mp hGU hg (Finset.mem_union_left _ hu)
    · rw [hUn]
      exact Finset.union_assoc _ _ _
  have hL0 : L 0 = ∅ := by simp [L,hF0,hM0]
  have hLT : L T = ∅ := by
    have ht := tail T le_rfl
    simp [L,ht.1,ht.2.1]
  have htail (i : ℕ) (hi : T ≤ i) : U i = U T ∧ L i = L T ∧ B i = ∅ := by
    have ht := tail i hi
    simp [L,B,ht.1,ht.2.1,ht.2.2.1,ht.2.2.2.1,ht.2.2.2.2,hLT]
  obtain ⟨life,hlife⟩ := extractLife T U L B D hU0 hL0 hlocalSource hLT htail
  have hAQ (i : ℕ) : A i ⊆ L i ∪ B i := by
    intro p hp
    by_cases hf : p ∈ F i
    · exact Finset.mem_union_right _ (Finset.mem_union_left _ hf)
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hp,hf⟩))
  have hMchar (i : ℕ) (p : P) :
      (p ∈ M i ↔ p ∈ L i ∪ B i ∧ p ∉ A i ∧ p ∉ B i) ∧
      (p ∈ (M i \ E i) ∪ G i ↔ p ∈ L i ∪ B i ∧ p ∉ A i ∧ p ∉ D i) := by
    have hF : p ∈ F i → p ∈ A i := fun hp => (rows i).1 hp
    have hA : p ∈ A i → p ∉ M i := fun hp => Finset.disjoint_left.mp (invariant i).1 hp
    have hG : p ∈ G i → p ∉ A i ∧ p ∉ M i := by
      intro hp
      have hh := Finset.disjoint_left.mp (prep i (invariant i).2).2.1 hp
      exact ⟨fun h => hh (Finset.mem_union_left _ h),fun h => hh (Finset.mem_union_right _ h)⟩
    have hE : p ∈ E i → p ∈ M i := fun hp => (rows i).2.2.2.1 hp
    simp only [L,B,D,Finset.mem_union,Finset.mem_sdiff]
    clear rows prep invariant hcon hlocalSource hlife hAQ htail hLT hL0 tail
    tauto
  refine ⟨life, ?_⟩
  intro p
  have hp := hlife p
  cases hspan : life p with
  | none =>
    simp only [hspan] at hp ⊢
    intro i
    have hq := (hp i).1
    refine ⟨fun ha => hq (hAQ i ha), ?_, ?_⟩
    · intro hm
      exact hq (Finset.mem_union_left _ (Finset.mem_union_right _ hm))
    · intro hg
      exact hq (Finset.mem_union_right _ (Finset.mem_union_right _ hg))
  | some az =>
    simp only [hspan] at hp ⊢
    refine ⟨hp.1,hp.2.1,?_,?_⟩
    · intro haz
      apply (hcon az.1).2.2
      exact Finset.mem_inter.mpr
        ⟨(hp.2.2 az.1).2.1.mpr rfl,(hp.2.2 az.1).2.2.mpr haz.symm⟩
    · intro i
      have hh := hp.2.2 i
      refine ⟨fun ha => hh.1.mp (hAQ i ha), ?_, ?_, hh.2.1,hh.2.2⟩
      · rw [(hMchar i p).1,hh.1,hh.2.1]
        by_cases ha : p ∈ A i
        · simp [ha]
        · simp only [ha,not_false_eq_true,true_and,and_true]
          omega
      · rw [(hMchar i p).2,hh.1,hh.2.2]
        by_cases ha : p ∈ A i
        · simp [ha]
        · simp only [ha,not_false_eq_true,true_and,and_true]
          omega

end Green64OrderedLift

end

/-! ## LiteralSourceHistory -/

section

open Classical
namespace Green64Literal

variable {P G : Type} [DecidableEq P] [Fintype G] {slots : G → ℕ}

structure LiteralHistory (N : ℕ) where
  rows : ℕ → SourceRow (P := P) G slots
  row_valid : ∀ i, i < N → RowValid (rows i)
  finalActive : List P
  finalPending : List P
  finalFresh : List P
  finalEver : Finset P
  globalValue : P → ℕ
  globalLabelGroup : P → G
  globalGroupV : G → ℝ
  globalBaseline : P → ℝ
  globalQ : ℝ
  globalRho : ℝ
  rho_positive : 0 < globalRho
  terminalEta : ℝ
  terminal_eta_eq : terminalEta = 1 - Real.sqrt globalQ
  prime_global : ∀ p, Nat.Prime (globalValue p)
  value_injective : Function.Injective globalValue
  row_value_eq : ∀ i, i < N → (rows i).value = globalValue
  row_group_eq : ∀ i, i < N → (rows i).labelGroup = globalLabelGroup
  row_group_v_eq : ∀ i, i < N → (rows i).groupV = globalGroupV
  row_baseline_eq : ∀ i, i < N → (rows i).baseline = globalBaseline
  row_rho_eq : ∀ i, i < N → (rows i).rho = globalRho
  row_q_eq : ∀ i, i < N → (rows i).q =
    if i = 0 then Real.sqrt globalQ else globalQ
  row_eta_eq : ∀ i, i < N → (rows i).eta = 1 - (rows i).q
  baseline_formula : ∀ p, globalBaseline p =
    1 - ((Finset.range N).sum (fun i => (rows i).eta) + terminalEta) /
      (globalValue p : ℝ)
  finalOffset : ℤ
  finalResidues : (p : P) → ZMod (globalValue p)
  final_pending_zero : ∀ p ∈ finalPending, finalResidues p = 0
  offset_link : ∀ i, i < N → (rows i).offsetAfter =
    (if i+1 < N then (rows (i+1)).offsetBefore else finalOffset)
  residue_link : ∀ i (hi : i < N) (p : P),
    cast (congrArg ZMod (congrFun (row_value_eq i hi) p))
      ((rows i).residueNext p) =
    (if hn : i+1 < N then
      cast (congrArg ZMod (congrFun (row_value_eq (i+1) hn) p))
        ((rows (i+1)).residueBefore p) else finalResidues p)
  initial_offset : (if 0 < N then (rows 0).offsetBefore else finalOffset) = 0
  initial_ever : (if 0 < N then (rows 0).everBornBefore else finalEver) = ∅
  initial_pending : (if 0 < N then (rows 0).pendingBefore else finalPending) = []
  initial_fresh :
    (if 0 < N then (rows 0).freshBefore else finalFresh) =
    (if 0 < N then (rows 0).active else finalActive)
  final_fresh_subset : finalFresh.toFinset ⊆ finalActive.toFinset
  final_fresh_new : Disjoint finalFresh.toFinset finalEver
  links_active : ∀ i, i < N →
    (rows i).nextActive =
      (if i+1 < N then (rows (i+1)).active else finalActive)
  links_pending : ∀ i, i < N →
    (rows i).pendingNext =
      (if i+1 < N then (rows (i+1)).pendingBefore else finalPending)
  links_fresh : ∀ i, i < N →
    (rows i).freshTarget =
      (if i+1 < N then (rows (i+1)).freshBefore else finalFresh)
  links_ever : ∀ i, i < N →
    (rows i).everBornAfter =
      (if i+1 < N then (rows (i+1)).everBornBefore else finalEver)

def visitActive {N : ℕ} (H : LiteralHistory (P := P) (G := G) (slots := slots) N)
    (i : ℕ) : List P :=
  if i < N then (H.rows i).active else if i = N then H.finalActive else []

def visitPending {N : ℕ} (H : LiteralHistory (P := P) (G := G) (slots := slots) N)
    (i : ℕ) : List P :=
  if i < N then (H.rows i).pendingBefore else if i = N then H.finalPending else []

def visitFresh {N : ℕ} (H : LiteralHistory (P := P) (G := G) (slots := slots) N)
    (i : ℕ) : List P :=
  if i < N then (H.rows i).freshBefore else if i = N then H.finalFresh else []

def visitEver {N : ℕ} (H : LiteralHistory (P := P) (G := G) (slots := slots) N)
    (i : ℕ) : Finset P :=
  if i < N then (H.rows i).everBornBefore
  else if i = N then H.finalEver else H.finalEver ∪ H.finalFresh.toFinset

def visitGhost {N : ℕ} (H : LiteralHistory (P := P) (G := G) (slots := slots) N)
    (i : ℕ) : Finset P :=
  if i < N then (H.rows i).ghostBatch.toFinset else ∅

def visitEnded {N : ℕ} (H : LiteralHistory (P := P) (G := G) (slots := slots) N)
    (i : ℕ) : Finset P :=
  if i < N then ended (H.rows i)
  else if i = N then H.finalPending.toFinset else ∅

def visitShared {N : ℕ} (H : LiteralHistory (P := P) (G := G) (slots := slots) N)
    (i : ℕ) : Finset P :=
  if i < N then shared (H.rows i) else ∅

def visitStored {N : ℕ} (H : LiteralHistory (P := P) (G := G) (slots := slots) N)
    (i : ℕ) : Finset P :=
  if i < N then stored (H.rows i) else ∅

def visitPromoted {N : ℕ} (H : LiteralHistory (P := P) (G := G) (slots := slots) N)
    (i : ℕ) : Finset P :=
  if i < N then promoted (H.rows i) else ∅



theorem frame_before {N : ℕ}
    (H : LiteralHistory (P := P) (G := G) (slots := slots) N)
    (i : ℕ) (hi : i < N) :
    visitActive H i = (H.rows i).active ∧
    visitPending H i = (H.rows i).pendingBefore ∧
    visitFresh H i = (H.rows i).freshBefore ∧
    visitEver H i = (H.rows i).everBornBefore ∧
    visitGhost H i = (H.rows i).ghostBatch.toFinset ∧
    visitEnded H i = ended (H.rows i) ∧
    visitShared H i = shared (H.rows i) ∧
    visitStored H i = stored (H.rows i) ∧
    visitPromoted H i = promoted (H.rows i) := by
  simp [visitActive, visitPending, visitFresh, visitEver,
    visitGhost, visitEnded, visitShared, visitStored, visitPromoted, hi]

theorem frame_next {N : ℕ}
    (H : LiteralHistory (P := P) (G := G) (slots := slots) N)
    (i : ℕ) (hi : i < N) :
    visitActive H (i+1) = (H.rows i).nextActive ∧
    visitPending H (i+1) = (H.rows i).pendingNext ∧
    visitFresh H (i+1) = (H.rows i).freshTarget ∧
    visitEver H (i+1) = (H.rows i).everBornAfter := by
  have heq (h : ¬ i+1 < N) : i+1 = N := by omega
  have hact := H.links_active i hi
  have hpend := H.links_pending i hi
  have hfresh := H.links_fresh i hi
  have hever := H.links_ever i hi
  by_cases h : i+1 < N
  · simp [visitActive, visitPending, visitFresh, visitEver, h] at *
    exact ⟨hact.symm,hpend.symm,hfresh.symm,hever.symm⟩
  · have hk := heq h
    simp [visitActive, visitPending, visitFresh, visitEver, h, hk] at *
    exact ⟨hact.symm,hpend.symm,hfresh.symm,hever.symm⟩

theorem terminal_frame {N : ℕ}
    (H : LiteralHistory (P := P) (G := G) (slots := slots) N) :
    visitActive H N = H.finalActive ∧
    visitPending H N = H.finalPending ∧
    visitFresh H N = H.finalFresh ∧
    visitEver H N = H.finalEver ∧
    visitGhost H N = ∅ ∧
    visitEnded H N = H.finalPending.toFinset ∧
    visitShared H N = ∅ ∧
    visitStored H N = ∅ ∧
    visitPromoted H N = ∅ := by
  simp [visitActive, visitPending, visitFresh, visitEver,
    visitGhost, visitEnded, visitShared, visitStored, visitPromoted]

theorem tail_frame {N : ℕ}
    (H : LiteralHistory (P := P) (G := G) (slots := slots) N)
    (i : ℕ) (hi : N < i) :
    visitActive H i = [] ∧
    visitPending H i = [] ∧
    visitFresh H i = [] ∧
    visitEver H i = H.finalEver ∪ H.finalFresh.toFinset ∧
    visitGhost H i = ∅ ∧
    visitEnded H i = ∅ ∧
    visitShared H i = ∅ ∧
    visitStored H i = ∅ ∧
    visitPromoted H i = ∅ := by
  have hn : ¬ i < N := by omega
  have hne : i ≠ N := by omega
  simp [visitActive, visitPending, visitFresh, visitEver,
    visitGhost, visitEnded, visitShared, visitStored, visitPromoted, hn, hne]



abbrev activeSet {N : ℕ}
    (H : LiteralHistory (P := P) (G := G) (slots := slots) N)
    (i : ℕ) : Finset P := (visitActive H i).toFinset

abbrev pendingSet {N : ℕ}
    (H : LiteralHistory (P := P) (G := G) (slots := slots) N)
    (i : ℕ) : Finset P := (visitPending H i).toFinset

abbrev freshSet {N : ℕ}
    (H : LiteralHistory (P := P) (G := G) (slots := slots) N)
    (i : ℕ) : Finset P := (visitFresh H i).toFinset

theorem operational_step_sets {N : ℕ}
    (H : LiteralHistory (P := P) (G := G) (slots := slots) N)
    (i : ℕ) (hi : i < N) :
    freshSet H i ⊆ activeSet H i ∧
    Disjoint (freshSet H i) (visitEver H i) ∧
    Disjoint (visitGhost H i) (visitEver H i ∪ freshSet H i) ∧
    visitEnded H i ⊆ pendingSet H i ∧
    visitShared H i ⊆ activeSet H i ∧
    visitStored H i ⊆ activeSet H i \ visitShared H i ∧
    visitPromoted H i ⊆
      (pendingSet H i \ visitEnded H i) ∪ visitGhost H i ∧
    activeSet H (i+1) =
      visitShared H i ∪ visitPromoted H i ∪ freshSet H (i+1) ∧
    pendingSet H (i+1) =
      (((pendingSet H i \ visitEnded H i) ∪ visitGhost H i) \
          visitPromoted H i) ∪ visitStored H i ∧
    visitEver H (i+1) =
      (visitEver H i ∪ freshSet H i) ∪ visitGhost H i := by
  let f := H.rows i
  have h : RowValid f := H.row_valid i hi
  have fb := frame_before H i hi
  have fn := frame_next H i hi
  have hA : activeSet H i = f.active.toFinset := congrArg List.toFinset fb.1
  have hM : pendingSet H i = f.pendingBefore.toFinset :=
    congrArg List.toFinset fb.2.1
  have hF : freshSet H i = f.freshBefore.toFinset :=
    congrArg List.toFinset fb.2.2.1
  have hU : visitEver H i = f.everBornBefore := fb.2.2.2.1
  have hG : visitGhost H i = f.ghostBatch.toFinset := fb.2.2.2.2.1
  have hE : visitEnded H i = ended f := fb.2.2.2.2.2.1
  have hS : visitShared H i = shared f := fb.2.2.2.2.2.2.1
  have hK : visitStored H i = stored f := fb.2.2.2.2.2.2.2.1
  have hR : visitPromoted H i = promoted f := fb.2.2.2.2.2.2.2.2
  have hA' : activeSet H (i+1) = f.nextActive.toFinset :=
    congrArg List.toFinset fn.1
  have hM' : pendingSet H (i+1) = f.pendingNext.toFinset :=
    congrArg List.toFinset fn.2.1
  have hF' : freshSet H (i+1) = f.freshTarget.toFinset :=
    congrArg List.toFinset fn.2.2.1
  have hU' : visitEver H (i+1) = f.everBornAfter := fn.2.2.2
  simp only [hA,hM,hF,hU,hG,hE,hS,hK,hR,hA',hM',hF',hU']
  have hparts := row_source_constraints f h
  refine ⟨h.fresh_before_active, h.fresh_before_unused, h.ghost_new,
    hparts.1, hparts.2.1, hparts.2.2.1, ?_, ?_, ?_, ?_⟩
  · rw [← row_ghost_support f h]
    exact hparts.2.2.2.1
  · exact row_target_support f h
  · simpa only [row_ghost_support f h] using row_pending_support f h
  · exact h.ever_update


theorem operational_terminal_sets {N : ℕ}
    (H : LiteralHistory (P := P) (G := G) (slots := slots) N) :
    freshSet H N ⊆ activeSet H N ∧
    Disjoint (freshSet H N) (visitEver H N) ∧
    Disjoint (visitGhost H N) (visitEver H N ∪ freshSet H N) ∧
    visitEnded H N ⊆ pendingSet H N ∧
    visitShared H N ⊆ activeSet H N ∧
    visitStored H N ⊆ activeSet H N \ visitShared H N ∧
    visitPromoted H N ⊆
      (pendingSet H N \ visitEnded H N) ∪ visitGhost H N ∧
    activeSet H (N+1) =
      visitShared H N ∪ visitPromoted H N ∪ freshSet H (N+1) ∧
    pendingSet H (N+1) =
      (((pendingSet H N \ visitEnded H N) ∪ visitGhost H N) \
          visitPromoted H N) ∪ visitStored H N ∧
    visitEver H (N+1) =
      (visitEver H N ∪ freshSet H N) ∪ visitGhost H N := by
  have ht := terminal_frame H
  have htail := tail_frame H (N+1) (by omega)
  have hA : activeSet H N = H.finalActive.toFinset :=
    congrArg List.toFinset ht.1
  have hM : pendingSet H N = H.finalPending.toFinset :=
    congrArg List.toFinset ht.2.1
  have hF : freshSet H N = H.finalFresh.toFinset :=
    congrArg List.toFinset ht.2.2.1
  have hU : visitEver H N = H.finalEver := ht.2.2.2.1
  have hG : visitGhost H N = ∅ := ht.2.2.2.2.1
  have hE : visitEnded H N = H.finalPending.toFinset := ht.2.2.2.2.2.1
  have hS : visitShared H N = ∅ := ht.2.2.2.2.2.2.1
  have hK : visitStored H N = ∅ := ht.2.2.2.2.2.2.2.1
  have hR : visitPromoted H N = ∅ := ht.2.2.2.2.2.2.2.2
  have hA' : activeSet H (N+1) = ∅ := by
    simp [activeSet, htail.1]
  have hM' : pendingSet H (N+1) = ∅ := by
    simp [pendingSet, htail.2.1]
  have hF' : freshSet H (N+1) = ∅ := by
    simp [freshSet, htail.2.2.1]
  have hU' : visitEver H (N+1) =
      H.finalEver ∪ H.finalFresh.toFinset := htail.2.2.2.1
  simp only [hA,hM,hF,hU,hG,hE,hS,hK,hR,hA',hM',hF',hU']
  simp [H.final_fresh_subset,H.final_fresh_new]


theorem operational_tail_sets {N : ℕ}
    (H : LiteralHistory (P := P) (G := G) (slots := slots) N)
    (i : ℕ) (hi : N < i) :
    freshSet H i ⊆ activeSet H i ∧
    Disjoint (freshSet H i) (visitEver H i) ∧
    Disjoint (visitGhost H i) (visitEver H i ∪ freshSet H i) ∧
    visitEnded H i ⊆ pendingSet H i ∧
    visitShared H i ⊆ activeSet H i ∧
    visitStored H i ⊆ activeSet H i \ visitShared H i ∧
    visitPromoted H i ⊆
      (pendingSet H i \ visitEnded H i) ∪ visitGhost H i ∧
    activeSet H (i+1) =
      visitShared H i ∪ visitPromoted H i ∪ freshSet H (i+1) ∧
    pendingSet H (i+1) =
      (((pendingSet H i \ visitEnded H i) ∪ visitGhost H i) \
          visitPromoted H i) ∪ visitStored H i ∧
    visitEver H (i+1) =
      (visitEver H i ∪ freshSet H i) ∪ visitGhost H i := by
  have ht := tail_frame H i hi
  have hn := tail_frame H (i+1) (by omega)
  have ha : activeSet H i = ∅ := by simp [activeSet,ht.1]
  have hm : pendingSet H i = ∅ := by simp [pendingSet,ht.2.1]
  have hf : freshSet H i = ∅ := by simp [freshSet,ht.2.2.1]
  have hu : visitEver H i = H.finalEver ∪ H.finalFresh.toFinset :=
    ht.2.2.2.1
  have hg : visitGhost H i = ∅ := ht.2.2.2.2.1
  have he : visitEnded H i = ∅ := ht.2.2.2.2.2.1
  have hs : visitShared H i = ∅ := ht.2.2.2.2.2.2.1
  have hk : visitStored H i = ∅ := ht.2.2.2.2.2.2.2.1
  have hr : visitPromoted H i = ∅ := ht.2.2.2.2.2.2.2.2
  have ha' : activeSet H (i+1) = ∅ := by simp [activeSet,hn.1]
  have hm' : pendingSet H (i+1) = ∅ := by simp [pendingSet,hn.2.1]
  have hf' : freshSet H (i+1) = ∅ := by simp [freshSet,hn.2.2.1]
  have hu' : visitEver H (i+1) =
      H.finalEver ∪ H.finalFresh.toFinset := hn.2.2.2.1
  simp only [ha,hm,hf,hu,hg,he,hs,hk,hr,ha',hm',hf',hu']
  simp

theorem operational_all_sets {N : ℕ}
    (H : LiteralHistory (P := P) (G := G) (slots := slots) N)
    (i : ℕ) :
    freshSet H i ⊆ activeSet H i ∧
    Disjoint (freshSet H i) (visitEver H i) ∧
    Disjoint (visitGhost H i) (visitEver H i ∪ freshSet H i) ∧
    visitEnded H i ⊆ pendingSet H i ∧
    visitShared H i ⊆ activeSet H i ∧
    visitStored H i ⊆ activeSet H i \ visitShared H i ∧
    visitPromoted H i ⊆
      (pendingSet H i \ visitEnded H i) ∪ visitGhost H i ∧
    activeSet H (i+1) =
      visitShared H i ∪ visitPromoted H i ∪ freshSet H (i+1) ∧
    pendingSet H (i+1) =
      (((pendingSet H i \ visitEnded H i) ∪ visitGhost H i) \
          visitPromoted H i) ∪ visitStored H i ∧
    visitEver H (i+1) =
      (visitEver H i ∪ freshSet H i) ∪ visitGhost H i := by
  by_cases hi : i < N
  · exact operational_step_sets H i hi
  · by_cases hz : i = N
    · subst i
      exact operational_terminal_sets H
    · exact operational_tail_sets H i (by omega)

theorem initial_sets {N : ℕ}
    (H : LiteralHistory (P := P) (G := G) (slots := slots) N) :
    visitEver H 0 = ∅ ∧ pendingSet H 0 = ∅ ∧
    freshSet H 0 = activeSet H 0 := by
  by_cases hn : 0 < N
  · simpa [visitEver,visitPending,visitFresh,visitActive,
      hn, pendingSet,freshSet,activeSet] using
      And.intro H.initial_ever
        (And.intro
          (congrArg List.toFinset H.initial_pending)
          (congrArg List.toFinset H.initial_fresh))
  · have hz : N = 0 := by omega
    subst N
    simpa [visitEver,visitPending,visitFresh,visitActive,
      pendingSet,freshSet,activeSet] using
      And.intro H.initial_ever
        (And.intro
          (congrArg List.toFinset H.initial_pending)
          (congrArg List.toFinset H.initial_fresh))

theorem tail_sets {N : ℕ}
    (H : LiteralHistory (P := P) (G := G) (slots := slots) N)
    (i : ℕ) (hi : N+1 ≤ i) :
    activeSet H i = ∅ ∧ pendingSet H i = ∅ ∧
    freshSet H i = ∅ ∧ visitGhost H i = ∅ ∧
    visitEver H i = visitEver H (N+1) := by
  have ht := tail_frame H i (by omega)
  have hn := tail_frame H (N+1) (by omega)
  simp [activeSet,pendingSet,freshSet,ht.1,ht.2.1,ht.2.2.1,
    ht.2.2.2.2.1,ht.2.2.2.1,hn.2.2.2.1]


theorem literal_history_lifespans
    [Fintype P] {N : ℕ}
    (H : LiteralHistory (P := P) (G := G) (slots := slots) N) :
    ∃ life : P → Option (ℕ × ℕ), ∀ p,
      match life p with
      | none => ∀ i, p ∉ activeSet H i ∧
          p ∉ pendingSet H i ∧ p ∉ visitGhost H i
      | some az => az.1 ≤ az.2 ∧ az.2 < N+1 ∧
          (az.1 = az.2 → p ∈ activeSet H az.1) ∧
          (∀ i,
            (p ∈ activeSet H i → az.1 ≤ i ∧ i ≤ az.2) ∧
            (p ∈ pendingSet H i ↔
              az.1 < i ∧ i ≤ az.2 ∧ p ∉ activeSet H i) ∧
            (p ∈ (pendingSet H i \ visitEnded H i) ∪ visitGhost H i ↔
              az.1 ≤ i ∧ i < az.2 ∧ p ∉ activeSet H i) ∧
            (p ∈ freshSet H i ∪ visitGhost H i ↔ az.1 = i) ∧
            (p ∈ visitEnded H i ∪
              (activeSet H i \ (visitShared H i ∪ visitStored H i)) ↔
                az.2 = i)) := by
  apply Green64OrderedLift.source_set_lifespans (N+1)
    (activeSet H) (pendingSet H) (freshSet H) (visitGhost H)
    (visitEnded H) (visitShared H) (visitStored H)
    (visitPromoted H) (visitEver H)
  · exact (initial_sets H).1
  · exact (initial_sets H).2.1
  · exact (initial_sets H).2.2
  · exact operational_all_sets H
  · intro i hi
    exact tail_sets H i hi

end Green64Literal

end

/-! ## LiteralProfileUnique -/

section

namespace Green64Literal

variable {P G : Type} [Fintype P] [DecidableEq P] [Fintype G]
variable {slots : G → ℕ} {N : ℕ}

def FitsHistory
    (H : LiteralHistory (P := P) (G := G) (slots := slots) N)
    (life : P → Option (ℕ × ℕ)) : Prop :=
  ∀ p, match life p with
    | none => ∀ i, p ∉ activeSet H i ∧
        p ∉ pendingSet H i ∧ p ∉ visitGhost H i
    | some az => az.1 ≤ az.2 ∧ az.2 < N+1 ∧
        (az.1 = az.2 → p ∈ activeSet H az.1) ∧
        (∀ i,
          (p ∈ activeSet H i → az.1 ≤ i ∧ i ≤ az.2) ∧
          (p ∈ pendingSet H i ↔
            az.1 < i ∧ i ≤ az.2 ∧ p ∉ activeSet H i) ∧
          (p ∈ (pendingSet H i \ visitEnded H i) ∪ visitGhost H i ↔
            az.1 ≤ i ∧ i < az.2 ∧ p ∉ activeSet H i) ∧
          (p ∈ freshSet H i ∪ visitGhost H i ↔ az.1 = i) ∧
          (p ∈ visitEnded H i ∪
            (activeSet H i \ (visitShared H i ∪ visitStored H i)) ↔
              az.2 = i))
theorem literal_history_unique_profile
    (H : LiteralHistory (P := P) (G := G) (slots := slots) N) :
    ∃! life : P → Option (ℕ × ℕ), FitsHistory H life := by
  obtain ⟨life, hraw⟩ := literal_history_lifespans H
  have hlife : FitsHistory H life := by
    exact hraw
  refine ⟨life, hlife, ?_⟩
  intro other hother
  funext p
  have hl := hlife p
  have ho := hother p
  cases he : life p with
  | none =>
    simp only [he] at hl ⊢
    cases hh : other p with
    | none => rfl
    | some bz =>
      simp only [hh] at ho
      have hb := (ho.2.2.2 bz.1).2.2.2.1.mpr rfl
      rcases Finset.mem_union.mp hb with hf | hg
      · exact False.elim ((hl bz.1).1 ((operational_all_sets H bz.1).1 hf))
      · exact False.elim ((hl bz.1).2.2 hg)
  | some az =>
    simp only [he] at hl ⊢
    cases hh : other p with
    | none =>
      simp only [hh] at ho
      have hb := (hl.2.2.2 az.1).2.2.2.1.mpr rfl
      rcases Finset.mem_union.mp hb with hf | hg
      · exact False.elim ((ho az.1).1 ((operational_all_sets H az.1).1 hf))
      · exact False.elim ((ho az.1).2.2 hg)
    | some bz =>
      simp only [hh] at ho
      have ha : bz.1 = az.1 :=
        (ho.2.2.2 az.1).2.2.2.1.mp
          ((hl.2.2.2 az.1).2.2.2.1.mpr rfl)
      have hz : bz.2 = az.2 :=
        (ho.2.2.2 az.2).2.2.2.2.mp
          ((hl.2.2.2 az.2).2.2.2.2.mpr rfl)
      exact congrArg some (Prod.ext ha hz)

end Green64Literal

end

/-! ## SourceCoefficients -/

section

open Classical
open scoped BigOperators

namespace Green64Literal

variable {P G : Type} [DecidableEq P] [Fintype G]
variable {slots : G → ℕ} {N : ℕ}

noncomputable def sourceMu (f : SourceRow (P := P) G slots) (p : P) : ℂ :=
  (1:ℂ) / ((f.groupV (f.labelGroup p):ℂ) *
    (f.value p : ℂ) * (f.baseline p : ℂ))

noncomputable def sourceGlobalMu
    (H : LiteralHistory (P := P) (G := G) (slots := slots) N)
    (p : P) : ℂ :=
  (1:ℂ) / ((H.globalGroupV (H.globalLabelGroup p):ℂ) *
    (H.globalValue p : ℂ) * (H.globalBaseline p : ℂ))

noncomputable def oldZeroIndices (f : SourceRow (P := P) G slots) :
    Finset (Fin f.pendingBefore.length) :=
  Finset.univ.filter (fun j => f.residueBefore (f.pendingBefore.get j) = 0)

noncomputable def visitZeroIndices (f : SourceRow (P := P) G slots) :
    Finset (Fin f.pendingAfter.length) :=
  Finset.univ.filter (fun j => f.residueAfter (f.pendingAfter.get j) = 0)

noncomputable def targetZeroIndices (f : SourceRow (P := P) G slots) :
    Finset (Fin f.pendingNext.length) :=
  Finset.univ.filter (fun j => f.residueNext (f.pendingNext.get j) = 0)
noncomputable def batchSize (f : SourceRow (P := P) G slots)
    (g : G) : ℕ :=
  (f.ghostBatch.filter (fun p => f.labelGroup p = g)).length

noncomputable def ghostWeight (f : SourceRow (P := P) G slots) : ℂ :=
  ((-(f.eta:ℂ) / (f.rho:ℂ)) ^ f.termIndices.card) *
  (((f.q:ℂ) / (f.rho:ℂ)^2) ^
    ((oldZeroIndices f).card - f.termIndices.card)) *
  (∏ g : G, ((1:ℂ) / (Nat.factorial (batchSize f g):ℂ)) *
    ((-(f.eta:ℂ) * (f.groupV g:ℂ) / (f.rho:ℂ)) ^ batchSize f g)) *
  (f.ghostBatch.map (sourceMu f)).prod

noncomputable def edgeSymmetryWeight (f : SourceRow (P := P) G slots) : ℂ :=
  ∏ g : G, ((1:ℂ) / (Nat.factorial (slots g) : ℂ))^2

noncomputable def orientedKernel (f : SourceRow (P := P) G slots) : ℂ :=
  let forward := f.kernelK *
    Complex.exp (Complex.I * (f.zeta:ℂ) * Complex.log (f.divisorD:ℂ))
  if f.orientation = 1 then forward else star forward

noncomputable def additivePhase (f : SourceRow (P := P) G slots) : ℂ :=
  Complex.exp ((2:ℂ) * (Real.pi:ℂ) * Complex.I *
    (f.theta:ℂ) * (f.orientation:ℂ) * (f.k:ℂ) * (f.divisorD:ℂ))
noncomputable def edgeWeight (f : SourceRow (P := P) G slots) : ℂ :=
  ((f.rho:ℂ) ^ (visitZeroIndices f).card) *
  ((f.rho:ℂ) ^ (targetZeroIndices f).card) *
  (∏ j : f.promotionSlots,
    ((1:ℂ) / (f.groupV (f.labelGroup (f.targetEndpoint.get j.val)):ℂ))) *
  (f.freshTarget.map (sourceMu f)).prod *
  (f.auxiliaryPrimes.map (fun p => (f.auxiliaryMeasure p : ℂ))).prod *
  edgeSymmetryWeight f * orientedKernel f * additivePhase f * f.smallFactor

noncomputable def literalRowWeight (f : SourceRow (P := P) G slots) : ℂ :=
  ghostWeight f * edgeWeight f

noncomputable def literalInitialWeight
    (H : LiteralHistory (P := P) (G := G) (slots := slots) N) : ℂ :=
  ((visitActive H 0).map (sourceGlobalMu H)).prod

noncomputable def literalTerminalWeight
    (H : LiteralHistory (P := P) (G := G) (slots := slots) N) : ℂ :=
  ((-H.terminalEta:ℝ) / H.globalRho : ℂ) ^ H.finalPending.length

noncomputable def literalPathWeight
    (H : LiteralHistory (P := P) (G := G) (slots := slots) N) : ℂ :=
  literalInitialWeight H *
    (∏ i ∈ Finset.range N, literalRowWeight (H.rows i)) *
      literalTerminalWeight H
theorem termIndices_subset_zeros (f : SourceRow (P := P) G slots)
    (h : RowValid f) : f.termIndices ⊆ oldZeroIndices f := by
  intro j hj
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h.term_zero j hj⟩

theorem sourceMu_eq_global
    (H : LiteralHistory (P := P) (G := G) (slots := slots) N)
    (i : ℕ) (hi : i < N) (p : P) :
    sourceMu (H.rows i) p = sourceGlobalMu H p := by
  simp [sourceMu,sourceGlobalMu,
    H.row_value_eq i hi, H.row_group_eq i hi,
    H.row_group_v_eq i hi,H.row_baseline_eq i hi]

theorem path_zero_edges
    (H : LiteralHistory (P := P) (G := G) (slots := slots) 0) :
    literalPathWeight H =
      literalInitialWeight H * literalTerminalWeight H := by
  simp [literalPathWeight]

end Green64Literal

end

/-! ## GhostLiteralBridge -/

section

open scoped BigOperators
open Classical

namespace Green64MemoryGhostOp

variable {P : Type} [Fintype P] [DecidableEq P]

/-- OLD-index deletion in G is identical to the SourceRow ordered-memory
    filter when the distinct-birth indicator gives no repeated labels.
    Without Nodup this replacement is deliberately NOT asserted. -/
theorem indexed_delete_eq_filter (old : List P) (hod : old.Nodup)
    (A : Finset (Fin old.length)) :
    ((List.finRange old.length).filter (fun j => j ∉ A)).map old.get =
      old.filter (fun p => p ∉ A.image old.get) := by
  have hinj : Function.Injective old.get :=
    List.nodup_iff_injective_get.mp hod
  have htest (j : Fin old.length) :
      (j ∉ A) ↔ (old.get j ∉ A.image old.get) := by
    constructor
    · intro hj hp
      obtain ⟨k,hk,hkj⟩ := Finset.mem_image.mp hp
      have he : k = j := hinj hkj
      exact hj (he ▸ hk)
    · intro hj hk
      exact hj (Finset.mem_image.mpr ⟨j,hk,rfl⟩)
  calc
    ((List.finRange old.length).filter (fun j => j ∉ A)).map old.get =
      ((List.finRange old.length).filter
        (fun j => old.get j ∉ A.image old.get)).map old.get := by
        congr 1
        apply List.filter_congr
        intro j hj
        simp only [htest]
    _ = ((List.finRange old.length).map old.get).filter
        (fun p => p ∉ A.image old.get) := by
        simpa [Function.comp_def] using
          (List.filter_map
            (f := old.get)
            (p := fun p : P => p ∉ A.image old.get)
            (l := List.finRange old.length)).symm
    _ = old.filter (fun p => p ∉ A.image old.get) := by
        rw [← List.ofFn_eq_map, List.ofFn_get]

/-- Faithful literal OLD-memory output for a selected G_i term.
    The terminal new-birth list is represented by its ordered Fin-index
    enumeration; the OLD indices are not replaced by fresh indices. -/
theorem afterGhost_eq_source_after
    {G : Type} [Fintype G] {slots : G → ℕ}
    (f : Green64Literal.SourceRow (P := P) G slots)
    (hf : Green64Literal.RowValid f) :
    afterGhost f.pendingBefore f.termIndices f.ghostBatch.get =
      f.pendingAfter := by
  unfold afterGhost
  rw [List.ofFn_get]
  rw [indexed_delete_eq_filter f.pendingBefore hf.pending_nodup f.termIndices]
  change f.pendingBefore.filter
    (fun p => p ∉ Green64Literal.ended f) ++ f.ghostBatch =
      f.pendingAfter
  exact hf.ghost_operation.symm

/-- Every selected OLD index has zero displacement as stipulated by
    source G_i; the literal RowValid conditions discharge the operator
    branch predicate without assuming the later physical profile. -/
theorem source_term_indices_valid
    {G : Type} [Fintype G] {slots : G → ℕ}
    (f : Green64Literal.SourceRow (P := P) G slots)
    (hf : Green64Literal.RowValid f) :
    f.termIndices ∈
      (zeroOld f.pendingBefore
        (fun p => f.residueBefore p = 0)).powerset := by
  apply Finset.mem_powerset.mpr
  intro j hj
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_univ _, hf.term_zero j hj⟩

/-- With the exact G_i raw operator residue predicate, the old-zero index
    count is the one already used in literal SourceCoefficients. -/
theorem old_zero_indices_match
    {G : Type} [Fintype G] {slots : G → ℕ}
    (f : Green64Literal.SourceRow (P := P) G slots) :
    zeroOld f.pendingBefore
      (fun p => f.residueBefore p = 0) =
        Green64Literal.oldZeroIndices f := by
  rfl

end Green64MemoryGhostOp

end

/-! ## GhostGroupBatches -/

section

open scoped BigOperators
open Classical

namespace Green64MemoryGhostOp

variable {P G : Type} [Fintype P] [DecidableEq P] [Fintype G]
variable {slots : G → ℕ}

/-- Independent source G_(i,g) ghost batches can be extracted from the
    single group-ordered literal ghost list. Requires the actual
    source row's group-label invariant; no set-valued shortcut. -/
theorem group_filtered_flatMap
    (l : List G) (hnodup : l.Nodup)
    (batch : G → List P) (group : P → G)
    (hgroup : ∀ g p, p ∈ batch g → group p = g)
    (g : G) :
    (l.flatMap batch).filter (fun p => group p = g) =
      if g ∈ l then batch g else [] := by
  have hfilter (h : G) :
      (batch h).filter (fun p => group p = g) =
        if h = g then batch h else [] := by
    by_cases hh : h = g
    · subst h
      simp only [ite_true]
      apply List.filter_eq_self.mpr
      intro p hp
      simp [hgroup g p hp]
    · simp only [if_neg hh]
      apply List.filter_eq_nil_iff.mpr
      intro p hp
      simp [hgroup h p hp, hh]
  induction l with
  | nil =>
      simp
  | cons h t ih =>
      have hnd := List.nodup_cons.mp hnodup
      have ht := ih hnd.2
      rw [List.flatMap_cons, List.filter_append, hfilter h, ht]
      by_cases he : h = g
      · subst g
        simp [hnd.1]
      · simp [he, Ne.symm he]

theorem literal_batchSize_eq_group_batch_length
    (f : Green64Literal.SourceRow (P := P) G slots)
    (hf : Green64Literal.RowValid f) (g : G) :
    Green64Literal.batchSize f g = (f.ghostBatches g).length := by
  unfold Green64Literal.batchSize
  rw [hf.ghost_group_order]
  have hgroups := group_filtered_flatMap (Finset.univ.toList)
    (Finset.nodup_toList (Finset.univ : Finset G)) f.ghostBatches f.labelGroup
    hf.ghost_group_labels g
  have hmerged :
      (List.flatMap f.ghostBatches (Finset.univ.toList)).filter
        (fun p => f.labelGroup p = g) = f.ghostBatches g := by
    simpa using hgroups
  exact congrArg List.length hmerged

/-- All ordered ghost-birth prime integration products factor by source
    group, with no additional V_g, factorial or free-label weight. -/
theorem literal_ghost_birth_measure_product
    (f : Green64Literal.SourceRow (P := P) G slots)
    (hf : Green64Literal.RowValid f) (nu : P → ℂ) :
    (f.ghostBatch.map nu).prod =
      ∏ g : G, ((f.ghostBatches g).map nu).prod := by
  rw [hf.ghost_group_order]
  simp only [List.map_flatMap, List.flatMap, List.prod_flatten]
  simp

/-- Literal source G_i factor is the product of:
    (a) its REAL old-zero index subset coefficient, and
    (b) each group's independent b_g! denominator and birth integral.
    This is the exact bridge from grouped operator to SourceCoefficients,
    not an assumed physical lifespan identity. -/
theorem source_ghost_group_coefficient
    (f : Green64Literal.SourceRow (P := P) G slots)
    (hf : Green64Literal.RowValid f) :
    Green64Literal.ghostWeight f =
      ((-((f.eta : ℂ)) / (f.rho : ℂ)) ^ f.termIndices.card) *
      (((f.q : ℂ) / (f.rho : ℂ)^2) ^
        ((Green64Literal.oldZeroIndices f).card - f.termIndices.card)) *
      (∏ g : G,
        ((1 : ℂ) / (Nat.factorial (f.ghostBatches g).length : ℂ)) *
        ((-((f.eta:ℂ)) * (f.groupV g : ℂ) / (f.rho:ℂ)) ^
          (f.ghostBatches g).length) *
        ((f.ghostBatches g).map (Green64Literal.sourceMu f)).prod) := by
  unfold Green64Literal.ghostWeight
  simp_rw [literal_batchSize_eq_group_batch_length f hf]
  rw [literal_ghost_birth_measure_product f hf]
  have hprod :
      ((∏ g : G,
          ((1:ℂ) / (Nat.factorial (f.ghostBatches g).length : ℂ)) *
          ((-((f.eta:ℂ)) * (f.groupV g:ℂ) / (f.rho:ℂ)) ^
            (f.ghostBatches g).length)) *
       (∏ g : G, ((f.ghostBatches g).map (Green64Literal.sourceMu f)).prod)) =
      ∏ g : G,
        (((1:ℂ) / (Nat.factorial (f.ghostBatches g).length : ℂ)) *
          ((-((f.eta:ℂ)) * (f.groupV g:ℂ) / (f.rho:ℂ)) ^
            (f.ghostBatches g).length)) *
          ((f.ghostBatches g).map (Green64Literal.sourceMu f)).prod := by
    exact Finset.prod_mul_distrib.symm
  rw [← hprod]
  ring

end Green64MemoryGhostOp

end

/-! ## GhostOldGroupFactors -/

section

open scoped BigOperators
open Classical

namespace Green64MemoryGhostOp

variable {I G : Type} [Fintype G] [DecidableEq I]

/-- Genuine partition of selected OLD-index choices by source group,
    including zero-sized groups and arbitrary finite index sets. -/
theorem group_card_filter_sum (s : Finset I) (group : I → G) :
    (∑ g : G, (s.filter (fun i => group i = g)).card) = s.card := by
  classical
  simp_rw [Finset.card_eq_sum_ones]
  simp_rw [Finset.sum_filter]
  rw [Finset.sum_comm]
  simp

theorem group_sdiff_filter
    (s t : Finset I) (group : I → G) (g : G) :
    ((s \ t).filter (fun i => group i = g)) =
      (s.filter (fun i => group i = g)) \
        (t.filter (fun i => group i = g)) := by
  classical
  ext i
  simp only [Finset.mem_filter, Finset.mem_sdiff]
  tauto

theorem group_card_sub
    (s t : Finset I) (group : I → G) (hst : t ⊆ s) :
    (∑ g : G, ((s.filter (fun i => group i = g)).card -
      (t.filter (fun i => group i = g)).card)) =
      s.card - t.card := by
  have hg (g : G) :
      (t.filter (fun i => group i = g)) ⊆
        (s.filter (fun i => group i = g)) := by
    intro i hi
    exact Finset.mem_filter.mpr
      ⟨hst (Finset.mem_filter.mp hi).1,(Finset.mem_filter.mp hi).2⟩
  have hdiff (g : G) :
      (s.filter (fun i => group i = g)).card -
        (t.filter (fun i => group i = g)).card =
      ((s \ t).filter (fun i => group i = g)).card := by
    rw [group_sdiff_filter]
    exact (Finset.card_sdiff_of_subset (hg g)).symm
  calc
    (∑ g : G, ((s.filter (fun i => group i = g)).card -
      (t.filter (fun i => group i = g)).card)) =
        ∑ g : G, ((s \ t).filter (fun i => group i = g)).card := by
          apply Finset.sum_congr rfl
          intro g hg
          exact hdiff g
    _ = (s \ t).card := group_card_filter_sum _ group
    _ = s.card - t.card := Finset.card_sdiff_of_subset hst

variable {P : Type} [Fintype P] [DecidableEq P]
variable {slots : G → ℕ}

noncomputable def groupSelected
    (f : Green64Literal.SourceRow (P := P) G slots) (g : G) :
    Finset (Fin f.pendingBefore.length) :=
  f.termIndices.filter (fun j => f.labelGroup (f.pendingBefore.get j) = g)

noncomputable def groupOldZeros
    (f : Green64Literal.SourceRow (P := P) G slots) (g : G) :
    Finset (Fin f.pendingBefore.length) :=
  (Green64Literal.oldZeroIndices f).filter
    (fun j => f.labelGroup (f.pendingBefore.get j) = g)

/-- Every source group has its own OLD-index subset, but the combined
    damping and termination factor equals the literal global OLD row
    coefficient without losing ordering or birth/termination distinction. -/
theorem literal_old_ghost_group_factor
    (f : Green64Literal.SourceRow (P := P) G slots)
    (hf : Green64Literal.RowValid f) :
    (∏ g : G,
       ((-((f.eta:ℂ)) / (f.rho:ℂ)) ^ (groupSelected f g).card) *
       (((f.q:ℂ) / (f.rho:ℂ)^2) ^
         ((groupOldZeros f g).card - (groupSelected f g).card))) =
     ((-((f.eta:ℂ)) / (f.rho:ℂ)) ^ f.termIndices.card) *
     (((f.q:ℂ) / (f.rho:ℂ)^2) ^
       ((Green64Literal.oldZeroIndices f).card - f.termIndices.card)) := by
  let γ : Fin f.pendingBefore.length → G :=
    fun j => f.labelGroup (f.pendingBefore.get j)
  let Z := Green64Literal.oldZeroIndices f
  have hsubset : f.termIndices ⊆ Z :=
    Green64Literal.termIndices_subset_zeros f hf
  have hα : (∑ g : G, (groupSelected f g).card) =
      f.termIndices.card := by
    simpa [groupSelected, γ] using group_card_filter_sum f.termIndices γ
  have hχ : (∑ g : G,
      ((groupOldZeros f g).card - (groupSelected f g).card)) =
      Z.card - f.termIndices.card := by
    simpa [groupOldZeros, groupSelected, γ, Z] using
      group_card_sub Z f.termIndices γ hsubset
  rw [Finset.prod_mul_distrib]
  rw [Finset.prod_pow_eq_pow_sum, Finset.prod_pow_eq_pow_sum]
  rw [hα,hχ]

end Green64MemoryGhostOp

end

/-! ## RawEdgeChoices -/

section

open Classical
open scoped BigOperators

namespace Green64RawEdge

variable {P G : Type} [DecidableEq P] [Fintype G]
variable {slots : G → ℕ}

/-- Independent RAW source E-edge branch choices. The frame f fixes sampled
source/target endpoint permutations, pattern, auxiliary labels and D, but
NOT the selected stores, promoted target slots, OLD injection, or fresh
target draws. They are all explicitly carried by this branch. -/
structure EdgeChoice (f : Green64Literal.SourceRow (P := P) G slots) where
  stores : Finset (Fin f.sourceEndpoint.length)
  promotionSlots : Finset (Fin f.targetEndpoint.length)
  promotionOld : promotionSlots ↪ Fin f.pendingAfter.length
  freshDraw : List P

/-- The actual branch from an admissible literal source row. -/
def sourceChoice (f : Green64Literal.SourceRow (P := P) G slots) : EdgeChoice f :=
  ⟨f.storeIndices, f.promotionSlots, f.promotionOld, f.freshTarget⟩

/-- The original edge step, fixed by orientation k and all source shared
plus independently drawn auxiliary labels forming D. -/
def edgeDelta (f : Green64Literal.SourceRow (P := P) G slots) : ℤ :=
  f.orientation * f.k * (f.divisorD : ℤ)

/-- OLD pending indices are selected BEFORE any newly stored labels are
appended. Their injection is into Fin pendingAfter.length, not into the
output list. -/
noncomputable def oldPromotionIndices
    (f : Green64Literal.SourceRow (P := P) G slots) (c : EdgeChoice f) :
    Finset (Fin f.pendingAfter.length) :=
  (Finset.univ : Finset c.promotionSlots).image c.promotionOld

noncomputable def rawPromotedNames
    (f : Green64Literal.SourceRow (P := P) G slots) (c : EdgeChoice f) :
    Finset P :=
  (oldPromotionIndices f c).image f.pendingAfter.get

/-- Store only the selected ordered source slots, after the visit G_i.
These particles cannot appear among the available OLD promotion indices
during this SAME edge. -/
noncomputable def rawStoredList
    (f : Green64Literal.SourceRow (P := P) G slots) (c : EdgeChoice f) :
    List P := Green64Literal.pick f.sourceEndpoint c.stores

/-- Discard promoted OLD indices by their *positions*, not by an
unchecked set of numerical prime values. Only then append freshly
stored source slots, preserving source order. -/
noncomputable def rawNextPending
    (f : Green64Literal.SourceRow (P := P) G slots) (c : EdgeChoice f) :
    List P :=
  ((List.finRange f.pendingAfter.length).filter
      (fun j => j ∉ oldPromotionIndices f c)).map f.pendingAfter.get ++
    rawStoredList f c

/-- Intermediate ordered target list before the sampled target endpoint
symmetrization: shared labels, promoted target slots, then independent
fresh draws. The true nextActive may be a permutation of this list. -/
noncomputable def rawNextActive
    (f : Green64Literal.SourceRow (P := P) G slots) (c : EdgeChoice f) :
    List P :=
  Green64Literal.pick f.sourceEndpoint f.sharedIndices ++
    Green64Literal.pick f.targetEndpoint c.promotionSlots ++ c.freshDraw

noncomputable def rawEdgeOutput
    (f : Green64Literal.SourceRow (P := P) G slots) (c : EdgeChoice f) :
    List P × List P :=
  (rawNextActive f c, rawNextPending f c)

/-- The induced residue of an output label is its translated OLD residue
when it survived, or the translated zero anchor when newly stored.
This formula does not read f.residueNext. -/
noncomputable def rawNextResidue
    (f : Green64Literal.SourceRow (P := P) G slots) (c : EdgeChoice f)
    (p : P) : ZMod (f.value p) :=
  if p ∈ (rawStoredList f c).toFinset then
    (edgeDelta f : ZMod (f.value p))
  else if p ∈ f.pendingAfter.toFinset \ rawPromotedNames f c then
    f.residueAfter p + (edgeDelta f : ZMod (f.value p))
  else 0

/-- This is an independent edge output state, not a copy of the
SourceRow.nextActive/nextPending fields. -/
noncomputable def rawNextZeroIndices
    (f : Green64Literal.SourceRow (P := P) G slots) (c : EdgeChoice f) :
    Finset (Fin (rawNextPending f c).length) :=
  Finset.univ.filter
    (fun j => rawNextResidue f c ((rawNextPending f c).get j) = 0)

theorem sourceChoice_stores
    (f : Green64Literal.SourceRow (P := P) G slots) :
    rawStoredList f (sourceChoice f) =
      Green64Literal.pick f.sourceEndpoint f.storeIndices := rfl

theorem sourceChoice_nextActive
    (f : Green64Literal.SourceRow (P := P) G slots) :
    rawNextActive f (sourceChoice f) =
      Green64Literal.pick f.sourceEndpoint f.sharedIndices ++
      Green64Literal.pick f.targetEndpoint f.promotionSlots ++
      f.freshTarget := rfl

theorem sourceChoice_nextActive_perm
    (f : Green64Literal.SourceRow (P := P) G slots)
    (hf : Green64Literal.RowValid f) :
    f.nextActive.Perm (rawNextActive f (sourceChoice f)) := by
  exact hf.target_operation

end Green64RawEdge

end

/-! ## RawEdgeMatching -/

section

open Classical
open scoped BigOperators

namespace Green64RawEdge

variable {P G : Type} [Fintype P] [DecidableEq P] [Fintype G] {slots : G → ℕ}

theorem rawPromotedNames_matches_target
    (f : Green64Literal.SourceRow (P := P) G slots) (c : EdgeChoice f)
    (hmatch : ∀ j : c.promotionSlots,
      f.targetEndpoint.get j.val = f.pendingAfter.get (c.promotionOld j)) :
    rawPromotedNames f c = c.promotionSlots.image f.targetEndpoint.get := by
  ext p
  constructor
  · intro hp
    obtain ⟨idx,hidx,heq⟩ := Finset.mem_image.mp hp
    obtain ⟨j,hj,hidxj⟩ := Finset.mem_image.mp hidx
    have hpnext : f.pendingAfter.get (c.promotionOld j) = p :=
      (congrArg f.pendingAfter.get hidxj).trans heq
    exact Finset.mem_image.mpr ⟨j.val,j.property,(hmatch j).trans hpnext⟩
  · intro hp
    obtain ⟨j,hj,hjp⟩ := Finset.mem_image.mp hp
    let jp : c.promotionSlots := ⟨j,hj⟩
    apply Finset.mem_image.mpr
    refine ⟨c.promotionOld jp, ?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨jp,Finset.mem_univ _,rfl⟩
    · exact (hmatch jp).symm.trans hjp

theorem sourceChoice_promotedNames
    (f : Green64Literal.SourceRow (P := P) G slots)
    (hf : Green64Literal.RowValid f) :
    rawPromotedNames f (sourceChoice f) =
      Green64Literal.promoted f := by
  have hm : ∀ j : (sourceChoice f).promotionSlots,
      f.targetEndpoint.get j.val =
        f.pendingAfter.get ((sourceChoice f).promotionOld j) := by
    intro j
    exact hf.promotion_matches j
  rw [rawPromotedNames_matches_target f (sourceChoice f) hm]
  rfl

theorem sourceChoice_nextPending
    (f : Green64Literal.SourceRow (P := P) G slots)
    (hf : Green64Literal.RowValid f) :
    rawNextPending f (sourceChoice f) = f.pendingNext := by
  unfold rawNextPending
  rw [Green64MemoryGhostOp.indexed_delete_eq_filter
      f.pendingAfter hf.pendingAfter_nodup (oldPromotionIndices f (sourceChoice f))]
  change f.pendingAfter.filter (fun p => p ∉ rawPromotedNames f (sourceChoice f)) ++
      rawStoredList f (sourceChoice f) = f.pendingNext
  rw [sourceChoice_promotedNames f hf]
  rw [sourceChoice_stores]
  exact hf.pending_operation.symm

theorem sourceChoice_output_exact
    (f : Green64Literal.SourceRow (P := P) G slots)
    (hf : Green64Literal.RowValid f) :
    f.nextActive.Perm (rawEdgeOutput f (sourceChoice f)).1 ∧
      (rawEdgeOutput f (sourceChoice f)).2 = f.pendingNext := by
  exact ⟨sourceChoice_nextActive_perm f hf, sourceChoice_nextPending f hf⟩

theorem promotion_old_indices_original_only
    (f : Green64Literal.SourceRow (P := P) G slots) (c : EdgeChoice f)
    (j : c.promotionSlots) :
    c.promotionOld j ∈ (Finset.univ : Finset (Fin f.pendingAfter.length)) :=
  Finset.mem_univ _

end Green64RawEdge

end

/-! ## RawEdgeResidues -/

section

open Classical
open scoped BigOperators

namespace Green64RawEdge

variable {P G : Type} [Fintype P] [DecidableEq P] [Fintype G] {slots : G → ℕ}

theorem edgeDelta_eq_offset
    (f : Green64Literal.SourceRow (P := P) G slots)
    (hf : Green64Literal.RowValid f) :
    edgeDelta f = f.offsetAfter - f.offsetBefore := by
  unfold edgeDelta
  rw [hf.offset_update]
  ring

theorem sourceChoice_storedSet
    (f : Green64Literal.SourceRow (P := P) G slots) :
    (rawStoredList f (sourceChoice f)).toFinset = Green64Literal.stored f := by
  simp [rawStoredList,sourceChoice,Green64Literal.pick_toFinset,Green64Literal.stored]

/-- Every literal output pending particle has exactly the displacement
constructed from the raw E operation: stored particles reset their anchor
and then translate by Delta; surviving OLD particles translate their old
residue. No appeal to a predeclared rawEdge weight is made. -/
theorem sourceChoice_nextResidue_correct
    (f : Green64Literal.SourceRow (P := P) G slots)
    (hf : Green64Literal.RowValid f)
    (p : P) (hp : p ∈ f.pendingNext) :
    rawNextResidue f (sourceChoice f) p = f.residueNext p := by
  have hstored := sourceChoice_storedSet f
  have hpromoted := sourceChoice_promotedNames f hf
  have hdelta := edgeDelta_eq_offset f hf
  unfold rawNextResidue
  rw [hstored, hpromoted]
  by_cases hs : p ∈ Green64Literal.stored f
  · simp only [hs, if_pos]
    rw [hdelta]
    exact (hf.store_reset p hs).symm
  · have hremain : p ∈ f.pendingAfter.toFinset \ Green64Literal.promoted f := by
      have hnext : p ∈
          f.pendingAfter.filter (fun q => q ∉ Green64Literal.promoted f) ++
          Green64Literal.pick f.sourceEndpoint f.storeIndices := by
        rw [hf.pending_operation] at hp
        exact hp
      rcases List.mem_append.mp hnext with hOld | hStore
      · have hh := List.mem_filter.mp hOld
        exact Finset.mem_sdiff.mpr ⟨List.mem_toFinset.mpr hh.1, by simpa using hh.2⟩
      · have hsets : p ∈ Green64Literal.stored f := by
          have hset : (Green64Literal.pick f.sourceEndpoint f.storeIndices).toFinset =
              Green64Literal.stored f := by
            rw [Green64Literal.pick_toFinset]
            rfl
          rw [← hset]
          exact List.mem_toFinset.mpr hStore
        exact (hs hsets).elim
    simp only [hs, if_neg, hremain, if_pos]
    rw [hdelta]
    exact (hf.surviving_translation p hremain).symm

theorem sourceChoice_zeroCount_exact
    (f : Green64Literal.SourceRow (P := P) G slots)
    (hf : Green64Literal.RowValid f) :
    (rawNextZeroIndices f (sourceChoice f)).card =
      (Green64Literal.targetZeroIndices f).card := by
  have hpending := sourceChoice_nextPending f hf
  unfold rawNextZeroIndices Green64Literal.targetZeroIndices
  rw [hpending]
  congr 1
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [sourceChoice_nextResidue_correct f hf
    (f.pendingNext.get j) (List.get_mem _ _)]

end Green64RawEdge

end

/-! ## RawEdgeValidity -/

section

open Classical
open scoped BigOperators

namespace Green64RawEdge

variable {P G : Type} [Fintype P] [DecidableEq P] [Fintype G] {slots : G → ℕ}

/-- Tests applied to independently chosen raw E edge operations. These
conditions are not a presupposed weighted identity. They enforce exactly
OLD-index injection legality, zero tests after Delta, nondivisibility
for stores and promotions, and target slot/output consistency. -/
structure EdgeAdmissible (f : Green64Literal.SourceRow (P := P) G slots)
    (c : EdgeChoice f) : Prop where
  stores_unshared : Disjoint f.sharedIndices c.stores
  promote_target : ∀ j : c.promotionSlots,
    f.targetEndpoint.get j.val = f.pendingAfter.get (c.promotionOld j)
  promoted_translated_zero : ∀ j : c.promotionSlots,
    f.residueAfter (f.pendingAfter.get (c.promotionOld j)) +
      (edgeDelta f : ZMod (f.value (f.pendingAfter.get (c.promotionOld j)))) = 0
  promoted_not_dividing : ∀ j : c.promotionSlots,
    ¬ f.value (f.pendingAfter.get (c.promotionOld j)) ∣ f.divisorD
  stored_not_dividing : ∀ j ∈ c.stores,
    ¬ f.value (f.sourceEndpoint.get j) ∣ f.divisorD
  target_permutation : f.nextActive.Perm (rawNextActive f c)
  fresh_nodup : c.freshDraw.Nodup
  pending_nodup : (rawNextPending f c).Nodup
  fresh_unused : Disjoint c.freshDraw.toFinset f.everBornAfter

/-- There is no extra factorial for a promotion injection:
its domain is exactly the selected ORDERED target slots, and it maps
injectively into the pre-store OLD list. -/
theorem old_promotion_injective
    (f : Green64Literal.SourceRow (P := P) G slots)
    (c : EdgeChoice f)
    (j k : c.promotionSlots) (h : c.promotionOld j = c.promotionOld k) :
    j = k := c.promotionOld.injective h

theorem sourceChoice_legal
    (f : Green64Literal.SourceRow (P := P) G slots)
    (hf : Green64Literal.RowValid f) :
    EdgeAdmissible f (sourceChoice f) := by
  refine ⟨hf.shared_store, ?_, ?_, ?_, ?_, hf.target_operation,
    hf.fresh_nodup, ?_, hf.next_fresh_unused⟩
  · intro j
    exact hf.promotion_matches j
  · intro j
    have hz := hf.promotion_zero j
    rw [hf.promotion_matches j] at hz
    rw [edgeDelta_eq_offset f hf]
    exact hz
  · intro j
    have hmatch := hf.promotion_matches j
    have hp : f.pendingAfter.get (f.promotionOld j) ∈ Green64Literal.promoted f := by
      apply Finset.mem_image.mpr
      refine ⟨j.val, j.property, ?_⟩
      rw [hmatch]
    exact hf.nondividing_promotion _ hp
  · intro j hj
    have hp : f.sourceEndpoint.get j ∈ Green64Literal.stored f :=
      Finset.mem_image.mpr ⟨j,hj,rfl⟩
    exact hf.nondividing_store _ hp
  · rw [sourceChoice_nextPending f hf]
    exact hf.pendingNext_nodup

end Green64RawEdge

end

/-! ## SourcePermutationAverage -/

section

open scoped BigOperators
open Classical

namespace Green64MemoryGhostOp

variable {G : Type} [Fintype G]

/-- The source E_i symmetrizes source and target endpoint slots
    INDEPENDENTLY in every group. -/
abbrev EndpointPerms (slots : G → ℕ) :=
  (g : G) → Equiv.Perm (Fin (slots g))

theorem source_perm_count (slots : G → ℕ) :
    Fintype.card (EndpointPerms slots) = ∏ g : G, (slots g).factorial := by
  simp [EndpointPerms, Fintype.card_pi, Fintype.card_perm]

theorem source_perm_pair_count (slots : G → ℕ) :
    Fintype.card (EndpointPerms slots × EndpointPerms slots) =
      (∏ g : G, (slots g).factorial)^2 := by
  rw [Fintype.card_prod, source_perm_count]
  ring

/-- Per-row endpoint permutation density from source E_i. Importantly
    this density is never *again* charged to the independent ghost-row
    factorial 1/b!. -/
noncomputable def sourceEndpointSymmetryWeight (slots : G → ℕ) : ℂ :=
  ∏ g : G, ((1:ℂ) / (Nat.factorial (slots g):ℂ))^2

noncomputable def doubleSourceSymmetrization (slots : G → ℕ)
    (w : EndpointPerms slots → EndpointPerms slots → ℂ) : ℂ :=
  sourceEndpointSymmetryWeight slots *
    (∑ σ : EndpointPerms slots,
      ∑ τ : EndpointPerms slots, w σ τ)

/-- Independent source and target permutations give EXACTLY their
    normalized double average. If and only if the integrand is
    permutation-independent can we replace it with a single coefficient
    without further work. -/
theorem source_double_symmetry_constant
    (slots : G → ℕ) (W : ℂ) :
    doubleSourceSymmetrization slots (fun _ _ => W) = W := by
  have hn (g : G) : ((Nat.factorial (slots g):ℂ)) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (slots g)
  have hnprod : (∏ g : G, ((Nat.factorial (slots g):ℂ))) ≠ 0 := by
    exact Finset.prod_ne_zero_iff.mpr (by intro g _; exact hn g)
  have hcast :
      ((∏ g : G, (slots g).factorial : ℕ) : ℂ) =
        ∏ g : G, ((slots g).factorial : ℂ) := by push_cast; rfl
  have hnorm : sourceEndpointSymmetryWeight slots =
      ((1 : ℂ) / (∏ g : G, ((slots g).factorial : ℂ)))^2 := by
    unfold sourceEndpointSymmetryWeight
    rw [Finset.prod_pow]
    simp only [one_div, Finset.prod_inv_distrib]
  unfold doubleSourceSymmetrization
  rw [hnorm]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [source_perm_count]
  rw [hcast]
  field_simp

theorem literal_edge_permutation_weight
    {P : Type} [DecidableEq P] {slots : G → ℕ}
    (f : Green64Literal.SourceRow (P := P) G slots) :
    Green64Literal.edgeSymmetryWeight f =
      sourceEndpointSymmetryWeight slots := by
  rfl

end Green64MemoryGhostOp

end

/-! ## RawEdgeCoefficients -/

section

open Classical
open scoped BigOperators

namespace Green64RawEdge

variable {P G : Type} [Fintype P] [DecidableEq P] [Fintype G] {slots : G → ℕ}

/-- Source's reciprocal-prime law is independently implemented here as
the probability integration weight assigned to each fresh target prime. -/
noncomputable def rawPrimeLaw (f : Green64Literal.SourceRow (P := P) G slots)
    (p : P) : ℂ :=
  (1:ℂ) / ((f.groupV (f.labelGroup p):ℂ) *
    (f.value p : ℂ) * (f.baseline p : ℂ))

theorem rawPrimeLaw_eq_sourceMu
    (f : Green64Literal.SourceRow (P := P) G slots) (p : P) :
    rawPrimeLaw f p = Green64Literal.sourceMu f p := rfl

/-- The actual OLD-pending-zero list at the input of E_i is the output
of the preceding G_i, before storing any source active labels. -/
noncomputable def rawInputZeroIndices
    (f : Green64Literal.SourceRow (P := P) G slots) :
    Finset (Fin f.pendingAfter.length) :=
  Finset.univ.filter (fun j => f.residueAfter (f.pendingAfter.get j) = 0)

theorem rawInputZero_eq_visitZero
    (f : Green64Literal.SourceRow (P := P) G slots) :
    rawInputZeroIndices f = Green64Literal.visitZeroIndices f := rfl

/-- Charge V_g^-1 for each selected OLD-index promotion, using the actual
label recovered from pendingAfter, not the sampled target slot's label. -/
noncomputable def rawPromotionWeight
    (f : Green64Literal.SourceRow (P := P) G slots) (c : EdgeChoice f) : ℂ :=
  ∏ j : c.promotionSlots,
    ((1:ℂ) / (f.groupV (f.labelGroup (f.pendingAfter.get (c.promotionOld j))) : ℂ))

/-- Independent free draws in E form D, and are not particle births.
The external source small-state factor is retained literally: the small
Hilbert/Haar operator is a distinct unproved integration obligation. -/
noncomputable def rawAuxiliaryFactor
    (f : Green64Literal.SourceRow (P := P) G slots) : ℂ :=
  (f.auxiliaryPrimes.map (fun p => (f.auxiliaryMeasure p : ℂ))).prod

/-- The source oriented kernel factor for K D^{i ζ}, with conjugation on
the reversed orientation. This does not impose a common kernel across rows
(needed later for instantiation of the actual source operator). -/
noncomputable def rawOrientedFactor
    (f : Green64Literal.SourceRow (P := P) G slots) : ℂ :=
  if f.orientation = 1 then
    f.kernelK * Complex.exp (Complex.I * (f.zeta:ℂ) *
      Complex.log (f.divisorD:ℂ))
  else
    star (f.kernelK * Complex.exp (Complex.I * (f.zeta:ℂ) *
      Complex.log (f.divisorD:ℂ)))

/-- The exact Fourier return-character phase e(θ σ k D). -/
noncomputable def rawReturnPhase
    (f : Green64Literal.SourceRow (P := P) G slots) : ℂ :=
  Complex.exp ((2:ℂ) * (Real.pi:ℂ) * Complex.I *
    (f.theta:ℂ) * (edgeDelta f : ℂ))

/-- This source edge branch weight does NOT read f.edgeWeight, targetZeroIndices
or f.residueNext. It computes the outgoing rho exponent from the raw NEW
state and its own translated residues. The chosen OLD-index promotion
injection supplies V_g^-1, and every fresh draw carries rawPrimeLaw. -/
noncomputable def rawEdgeTerm
    (f : Green64Literal.SourceRow (P := P) G slots) (c : EdgeChoice f) : ℂ :=
  ((f.rho:ℂ) ^ (rawInputZeroIndices f).card) *
  ((f.rho:ℂ) ^ (rawNextZeroIndices f c).card) *
  rawPromotionWeight f c *
  (c.freshDraw.map (rawPrimeLaw f)).prod *
  rawAuxiliaryFactor f *
  Green64MemoryGhostOp.sourceEndpointSymmetryWeight slots *
  rawOrientedFactor f * rawReturnPhase f * f.smallFactor

theorem sourceChoice_promotionWeight
    (f : Green64Literal.SourceRow (P := P) G slots)
    (hf : Green64Literal.RowValid f) :
    rawPromotionWeight f (sourceChoice f) =
      ∏ j : f.promotionSlots,
       ((1:ℂ) / (f.groupV (f.labelGroup (f.targetEndpoint.get j.val)) : ℂ)) := by
  unfold rawPromotionWeight
  change (∏ j : f.promotionSlots,
       ((1:ℂ) / (f.groupV (f.labelGroup (f.pendingAfter.get (f.promotionOld j))) : ℂ))) = _
  apply Finset.prod_congr rfl
  intro j hj
  rw [hf.promotion_matches j]

theorem rawOrientedFactor_eq
    (f : Green64Literal.SourceRow (P := P) G slots) :
    rawOrientedFactor f = Green64Literal.orientedKernel f := by
  rfl

theorem rawReturnPhase_eq
    (f : Green64Literal.SourceRow (P := P) G slots) :
    rawReturnPhase f = Green64Literal.additivePhase f := by
  unfold rawReturnPhase Green64Literal.additivePhase edgeDelta
  congr 1
  push_cast
  ring

/-- The independently selected source RAW E edge exactly has the full
complex literal source coefficient: OLD and output rho, V promotions,
fresh-prime integrations, auxiliary draws, two sampled permutation
densities, oriented K D^{iζ}, additive phase and small-state factor.
No conclusion of Exact Memory Identity is assumed. -/
theorem sourceChoice_rawEdgeTerm_eq
    (f : Green64Literal.SourceRow (P := P) G slots)
    (hf : Green64Literal.RowValid f) :
    rawEdgeTerm f (sourceChoice f) = Green64Literal.edgeWeight f := by
  unfold rawEdgeTerm Green64Literal.edgeWeight
  rw [rawInputZero_eq_visitZero,
      sourceChoice_zeroCount_exact f hf,
      sourceChoice_promotionWeight f hf]
  rw [rawOrientedFactor_eq,rawReturnPhase_eq]
  rfl

end Green64RawEdge

end

/-! ## PhysicalSourceExactScalar -/

section

open Classical
open scoped BigOperators

namespace Green64FullPhysicalE

/-- The original source complex K_nu D^(i zeta), with conjugation
when the signed source orientation is not the positive direction.
This is NOT a free abstract physical edge multiplier. -/
noncomputable def originalOrientedKernel
    (Knu : ℂ) (zeta : ℝ) (D : ℕ) (orientation : ℤ) : ℂ :=
  if orientation = 1 then
    Knu * Complex.exp (Complex.I * (zeta : ℂ) *
      Complex.log (D : ℂ))
  else
    star (Knu * Complex.exp (Complex.I * (zeta : ℂ) *
      Complex.log (D : ℂ)))

/-- Source Fourier return phase exp(2 pi i theta sigma k D),
with the exact integer signed displacement Delta=sigma*k*D. -/
noncomputable def originalReturnPhase
    (theta : ℝ) (orientation k : ℤ) (D : ℕ) : ℂ :=
  Complex.exp ((2 : ℂ) * (Real.pi : ℂ) * Complex.I *
    (theta : ℂ) *
    ((orientation * k * (D : ℤ)) : ℂ))

noncomputable def originalEdgeScalar
    (Knu : ℂ) (zeta theta : ℝ)
    (D : ℕ) (orientation k : ℤ) : ℂ :=
  originalOrientedKernel Knu zeta D orientation *
    originalReturnPhase theta orientation k D

/-- CHECK AGAINST THE ACTUAL FROZEN SOURCE LITERAL ROW
(not a newly invented matrix scalar): our spectral/phase E_i
coefficient is definitionally the RAW original K_nu D^(i zeta)
times e(theta sigma kD), in both orientations. -/
theorem originalEdgeScalar_matches_literal_raw
    {P G : Type} [Fintype G]
    {slots : G → ℕ}
    (f : Green64Literal.SourceRow (P := P) G slots) :
    originalEdgeScalar f.kernelK f.zeta f.theta
      f.divisorD f.orientation f.k =
    Green64RawEdge.rawOrientedFactor f *
      Green64RawEdge.rawReturnPhase f := by
  unfold originalEdgeScalar originalOrientedKernel originalReturnPhase
    Green64RawEdge.rawOrientedFactor Green64RawEdge.rawReturnPhase
    Green64RawEdge.edgeDelta
  push_cast
  rfl

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)]
variable [∀ g, DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ)
variable [∀ g, ∀ p, NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)]
variable [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ)
variable [∀ g, ∀ p, NeZero (bigMod g p)]
variable (M : ℕ) (cap : BG → ℕ)

/-- Insert the source exact K_nu D^(i zeta) Fourier phase once
in the actual all-small Haar/big Fock E kernel. Source Knu can
depend on both endpoint permutation families, source shared/free
labels and fixed D; the remaining sampling law for D is open. -/
noncomputable def originalGlobalSourceK
    (x : FullPhysicalState SP smallMod BP bigMod M cap)
    (Knu : GlobalSourceK SP smallMod BP bigMod M cap x)
    (zeta theta : ℝ) (D : ℕ)
    (orientation k : ℤ) :
    GlobalSourceK SP smallMod BP bigMod M cap x :=
  fun sigBig tauBig bigChoice sigSmall tauSmall =>
    originalEdgeScalar
      (Knu sigBig tauBig bigChoice sigSmall tauSmall)
      zeta theta D orientation k

theorem originalGlobalSourceK_applied
    (x : FullPhysicalState SP smallMod BP bigMod M cap)
    (Knu : GlobalSourceK SP smallMod BP bigMod M cap x)
    (zeta theta : ℝ) (D : ℕ) (orientation k : ℤ)
    (sigBig tauBig : BigGroupPerm (BG := BG) M)
    (bigChoice : BigGroupBranch BP bigMod M cap x.2)
    (sigSmall tauSmall : Green64SmallHaar.GroupPermFamily (G := SG) M) :
    originalGlobalSourceK SP smallMod BP bigMod M cap x
      Knu zeta theta D orientation k
      sigBig tauBig bigChoice sigSmall tauSmall =
    originalEdgeScalar
      (Knu sigBig tauBig bigChoice sigSmall tauSmall)
      zeta theta D orientation k := rfl

end Green64FullPhysicalE

end

/-! ## ReturnCharacter -/

section

open Classical MeasureTheory
open scoped BigOperators
noncomputable section
namespace Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 3000000

/-- The exact original integer return character. This is the internal
physical-position Fourier variable, not either D61 endpoint Fourier measure. -/
def b648ReturnCharacter434 (theta : ℝ) (d : ℤ) : ℂ :=
  Complex.exp ((2:ℂ)*(Real.pi:ℂ)*Complex.I*(theta:ℂ)*(d:ℂ))

theorem b648_return_character_add434 (theta : ℝ) (a b : ℤ) :
    b648ReturnCharacter434 theta (a+b)=
      b648ReturnCharacter434 theta a*b648ReturnCharacter434 theta b := by
  unfold b648ReturnCharacter434
  rw [Int.cast_add,mul_add,Complex.exp_add]

theorem b648_return_character_product434 {ι : Type} [DecidableEq ι]
    (s : Finset ι) (d : ι → ℤ) (theta : ℝ) :
    (∏ i ∈ s,b648ReturnCharacter434 theta (d i))=
      b648ReturnCharacter434 theta (∑ i ∈ s,d i) := by
  induction s using Finset.induction_on with
  | empty => simp [b648ReturnCharacter434]
  | insert i s hi ih =>
    rw [Finset.prod_insert hi,Finset.sum_insert hi,ih,b648_return_character_add434]

theorem b648_return_character_continuous434 (d : ℤ) :
    Continuous (fun theta : ℝ => b648ReturnCharacter434 theta d) := by
  unfold b648ReturnCharacter434
  fun_prop

/-- Exact real unit-interval projector for physical position return.
The entire oscillatory integral is evaluated before any norm is taken. -/
theorem b648_return_character_integral434 (d : ℤ) :
    (∫ theta : ℝ in (0:ℝ)..1,b648ReturnCharacter434 theta d)=if d=0 then 1 else 0 := by
  by_cases hd : d=0
  · subst d
    simp [b648ReturnCharacter434]
  · rw [ite_eq_right hd]
    let c : ℂ := (2:ℂ)*(Real.pi:ℂ)*Complex.I*(d:ℂ)
    have hpi : (Real.pi:ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    have hdC : (d:ℂ) ≠ 0 := by exact_mod_cast hd
    have hc : c ≠ 0 := mul_ne_zero (mul_ne_zero
      (mul_ne_zero (by norm_num) hpi) Complex.I_ne_zero) hdC
    have hf : (fun theta : ℝ => b648ReturnCharacter434 theta d)=
        fun theta : ℝ => Complex.exp (c*(theta:ℂ)) := by
      funext theta
      unfold b648ReturnCharacter434 c
      congr 1
      ring
    rw [hf,integral_exp_mul_complex hc]
    have he : Complex.exp c=1 := by
      convert Complex.exp_int_mul_two_pi_mul_I d using 1
      congr 1
      ring
    simp only [Complex.ofReal_one,Complex.ofReal_zero,mul_one,mul_zero,Complex.exp_zero,he,sub_self,zero_div]

/-- The original Knu D^(i zeta) and its exact orientation are unchanged;
only the literal integer displacement phase depends on theta. -/
theorem b648_original_edge_theta434 (Knu : ℂ) (zeta theta : ℝ)
    (D : ℕ) (orientation k : ℤ) :
    originalEdgeScalar Knu zeta theta D orientation k =
      originalEdgeScalar Knu zeta 0 D orientation k *
        b648ReturnCharacter434 theta (orientation*k*(D:ℤ)) := by
  simp [originalEdgeScalar,originalReturnPhase,b648ReturnCharacter434]
end Green64FullPhysicalE

end

end

/-! ## PhysicalSourceSharedDivisor -/

section

open Classical
open scoped BigOperators

namespace Green64FullPhysicalE

variable {P G : Type} [Fintype G] [DecidableEq P]
variable {slots : G → ℕ}

/-- In an ACTUAL original source row D contains the product of
ALL shared BIG prime values. This bridges fixed-D physical edges
to the source divisor construction, rather than assuming shared
p | D as an unproved extra physical kernel hypothesis. -/
theorem source_shared_big_prime_divides_D
    (f : Green64Literal.SourceRow (P := P) G slots)
    (hf : Green64Literal.RowValid f)
    (p : P) (hp : p ∈ Green64Literal.shared f) :
    f.value p ∣ f.divisorD := by
  obtain ⟨i, hi, hpi⟩ := Finset.mem_image.mp hp
  have hdiv : f.value p ∣
      ∏ j ∈ f.sharedIndices, f.value (f.sourceEndpoint.get j) := by
    rw [← hpi]
    exact Finset.dvd_prod_of_mem
      (s := f.sharedIndices) (f := fun j => f.value (f.sourceEndpoint.get j)) hi

  have hprod :
      ((Green64Literal.pick f.sourceEndpoint f.sharedIndices).map f.value).prod =
      ∏ j ∈ f.sharedIndices, f.value (f.sourceEndpoint.get j) := by
    simp [Green64Literal.pick, List.map_map, Finset.prod_toList]
  obtain ⟨c, hc⟩ := hdiv
  rw [hf.divisor_from_groups, hprod]
  refine ⟨(f.smallSharedPrimes.prod * f.smallAuxiliaryPrimes.prod) *
      c * (f.auxiliaryPrimes.map f.value).prod, ?_⟩
  rw [hc]
  ring

end Green64FullPhysicalE

end

/-! ## PhysicalSourcePatternE -/

section

open Classical
open scoped BigOperators

namespace Green64FullPhysicalE

/-- The source prescribes free C_g only among the first J slots
of each BIG group; all SMALL groups have C_g = empty. -/
structure SourcePattern (BG : Type) (J m : ℕ) where
  free : BG → Finset (Fin J)
  free_bound : ∀ g, (free g).card ≤ m

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)]
variable [∀ g, DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ)
variable [∀ g, ∀ p, NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)]
variable [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ)
variable [∀ g, ∀ p, NeZero (bigMod g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)

noncomputable def sourceSmallShared :
    SG → Finset (Fin (J + ell)) :=
  fun _ => Finset.univ.filter (fun i => i.val < J)
noncomputable def sourceBigShared
    (pat : SourcePattern BG J m) :
    BG → Finset (Fin (J + ell)) :=
  fun g => Finset.univ.filter (fun i =>
    i.val < J ∧ i.val ∉ (pat.free g).image Fin.val)

/-- Exactly one independent auxiliary µ_g prime draw per C_g slot;
there is no dummy sample in non-free positions. -/
abbrev SourceBigAux (pat : SourcePattern BG J m) :=
  (g : BG) → (↥(pat.free g)) → BP g

noncomputable instance (pat : SourcePattern BG J m) :
    Fintype (SourceBigAux BP J m pat) := inferInstance

/-- Original (not baseline-tilted) auxiliary law 1/(V_g p);
auxiliary labels can repeat, but are banned from endpoint lists. -/
noncomputable def sourceAuxMass (Vbig : BG → ℝ)
    (pat : SourcePattern BG J m)
    (aux : SourceBigAux BP J m pat) : ℝ :=
  ∏ g : BG, ∏ j : ↥(pat.free g),
    1 / (Vbig g * (bigMod g (aux g j) : ℝ))

/-- Original D = D_small D_big. Small C_g are empty;
big free factors are independently drawn and may coincide. -/
noncomputable def sourcePhysicalD
    (pat : SourcePattern BG J m)
    (aux : SourceBigAux BP J m pat)
    (x : FullPhysicalState SP smallMod BP bigMod (J + ell) cap) : ℕ :=
  (∏ g : SG, ∏ i ∈ sourceSmallShared J ell g,
    smallMod g (Green64SmallHaar.marks (smallMod g) (J + ell) (x.1 g) i)) *
  (∏ g : BG,
    (∏ i ∈ sourceBigShared J ell m pat g,
      bigMod g ((x.2 g).1 i)) *
    (∏ j : ↥(pat.free g), bigMod g (aux g j)))

/-- The source forbids every free auxiliary label of D from BOTH
active endpoints. The auxiliary labels are not required distinct. -/
def sourceAuxAvoidsEndpoints
    (pat : SourcePattern BG J m)
    (aux : SourceBigAux BP J m pat)
    (x : FullPhysicalState SP smallMod BP bigMod (J + ell) cap)
    (b : FullPhysicalEdgeBranch SP smallMod BP bigMod (J + ell) cap x) :
    Prop :=
  ∀ (g : BG) (j : ↥(pat.free g)) (i : Fin (J + ell)),
    aux g j ≠ (x.2 g).1 i ∧ aux g j ≠ (b.bigChoice g).1 i
variable {Nu : Type} [Fintype Nu]
variable (patterns : Nu → SourcePattern BG J m)

/-- A source-wide choice really contains its pattern ν, all its
independent auxiliary D draws and a PHYSICAL (not postulated)
big/small endpoint/store/promotion/fresh branch. -/
abbrev SourcePhysicalChoice
    (x : FullPhysicalState SP smallMod BP bigMod (J + ell) cap) :=
  Σ nu : Nu, (SourceBigAux BP J m (patterns nu)) ×
    FullPhysicalEdgeBranch SP smallMod BP bigMod (J + ell) cap x

noncomputable instance
    (x : FullPhysicalState SP smallMod BP bigMod (J + ell) cap) :
    Fintype (SourcePhysicalChoice SP smallMod BP bigMod J ell m cap patterns x) :=
  inferInstance

/-- This input K_ν reads ONLY independently permuted BIG source
and target ordered labels and the BIG auxiliary draws, as in TeX.
It cannot read any SMALL or pending-memory data. -/
abbrev SourcePatternK :=
  (nu : Nu) → SourceBigAux BP J m (patterns nu) →
    ((g : BG) → Fin (J + ell) → BP g) →
    ((g : BG) → Fin (J + ell) → BP g) → ℂ

noncomputable def sourcePatternGlobalK
    (Knu : SourcePatternK BP J ell m patterns)
    (x : FullPhysicalState SP smallMod BP bigMod (J + ell) cap)
    (nu : Nu) (aux : SourceBigAux BP J m (patterns nu))
    (zeta theta : ℝ) (orientation k : ℤ) :
    GlobalSourceK SP smallMod BP bigMod (J + ell) cap x :=
  originalGlobalSourceK SP smallMod BP bigMod (J + ell) cap x
    (fun sigma tau branch _ _ =>
      Knu nu aux
        (fun g i => (x.2 g).1 (sigma g i))
        (fun g i => (branch g).1 (tau g i)))
    zeta theta
    (sourcePhysicalD SP smallMod BP bigMod J ell m cap
      (patterns nu) aux x)
    orientation k

noncomputable def sourcePhysicalStep
    (pat : SourcePattern BG J m)
    (aux : SourceBigAux BP J m pat)
    (x : FullPhysicalState SP smallMod BP bigMod (J + ell) cap)
    (orientation k : ℤ) : ℤ :=
  orientation * k *
    (sourcePhysicalD SP smallMod BP bigMod J ell m cap pat aux x : ℤ)
/-- Admissible GLOBAL source choices: all-pattern sum, independent
D draws, exact shared-copy tests, OLD-only promotions, rho/stores,
p∤D, finite Fock bounds, small Haar, plus the auxiliary ban. -/
def SourcePhysicalLegal
    (x : FullPhysicalState SP smallMod BP bigMod (J + ell) cap)
    (orientation k : ℤ)
    (z : SourcePhysicalChoice SP smallMod BP bigMod
      J ell m cap patterns x) : Prop :=
  let pat := patterns z.1
  let aux := z.2.1
  FullPhysicalEdgeLegal SP smallMod BP bigMod (J + ell) cap
      x (sourceBigShared J ell m pat)
      (sourcePhysicalD SP smallMod BP bigMod J ell m cap pat aux x)
      (sourcePhysicalStep SP smallMod BP bigMod J ell m cap
        pat aux x orientation k) z.2.2 ∧
    sourceAuxAvoidsEndpoints SP smallMod BP bigMod J ell m cap
      pat aux x z.2.2 ∧
    (orientation = 1 ∨ orientation = -1) ∧ k ≠ 0

noncomputable def legalSourcePhysicalChoices
    (x : FullPhysicalState SP smallMod BP bigMod (J + ell) cap)
    (orientation k : ℤ) :
    Finset (SourcePhysicalChoice SP smallMod BP bigMod
      J ell m cap patterns x) :=
  Finset.univ.filter
    (SourcePhysicalLegal SP smallMod BP bigMod J ell m cap
      patterns x orientation k)

noncomputable def sourcePhysicalOutput
    (x : FullPhysicalState SP smallMod BP bigMod (J + ell) cap)
    (orientation k : ℤ)
    (z : SourcePhysicalChoice SP smallMod BP bigMod
      J ell m cap patterns x) :
    FullPhysicalOutput SP smallMod BP bigMod (J + ell) :=
  fullPhysicalBranchOutput SP smallMod BP bigMod (J + ell) cap x
    (sourcePhysicalStep SP smallMod BP bigMod J ell m cap
      (patterns z.1) z.2.1 x orientation k) z.2.2

/-- The only auxiliary factor is genuine independent original µ_g
sampling. Endpoint factors remain inside the existing checked
big-active/Fock/small-Haar physical branch coefficient. -/
noncomputable def sourcePhysicalCoefficient
    (q rho : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (muBig : (g : BG) → BP g → ℝ)
    (Knu : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (orientation k : ℤ)
    (x : FullPhysicalState SP smallMod BP bigMod (J + ell) cap)
    (z : SourcePhysicalChoice SP smallMod BP bigMod
      J ell m cap patterns x) : ℂ :=
  (sourceAuxMass BP bigMod J m Vbig (patterns z.1) z.2.1 : ℂ) *
    fullPhysicalBranchCoefficient SP smallMod BP bigMod
      (J + ell) cap q rho Vsmall Vbig muBig x
      (sourceSmallShared J ell)
      (sourceBigShared J ell m (patterns z.1))
      (sourcePhysicalStep SP smallMod BP bigMod J ell m cap
        (patterns z.1) z.2.1 x orientation k)
      (sourcePatternGlobalK SP smallMod BP bigMod
        J ell m cap patterns Knu x z.1 z.2.1
        zeta theta orientation k) z.2.2
/-- The actual source-wide FINITE physical E_i at memory cutoff:
not a fixed-D kernel and not an abstract Markov transition.
Every pattern, auxiliary D draw, endpoint permutation, OLD
injection, fresh label, small Haar and coupled K is enumerated. -/
noncomputable def fullSourcePhysicalE
    (q rho : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (muBig : (g : BG) → BP g → ℝ)
    (Knu : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (orientation k : ℤ)
    (x : FullPhysicalState SP smallMod BP bigMod (J + ell) cap)
    (F : FullPhysicalOutput SP smallMod BP bigMod (J + ell) → ℂ) : ℂ :=
  ∑ z ∈ legalSourcePhysicalChoices SP smallMod BP bigMod
      J ell m cap patterns x orientation k,
    sourcePhysicalCoefficient SP smallMod BP bigMod J ell m cap
      patterns q rho Vsmall Vbig muBig Knu zeta theta
      orientation k x z *
    F (sourcePhysicalOutput SP smallMod BP bigMod J ell m cap
      patterns x orientation k z)

noncomputable def fullSourcePhysicalSupport
    (x : FullPhysicalState SP smallMod BP bigMod (J + ell) cap)
    (orientation k : ℤ) :
    Finset (FullPhysicalOutput SP smallMod BP bigMod (J + ell)) :=
  (legalSourcePhysicalChoices SP smallMod BP bigMod J ell m cap
    patterns x orientation k).image
    (sourcePhysicalOutput SP smallMod BP bigMod J ell m cap
      patterns x orientation k)

noncomputable def fullSourcePhysicalKernel
    (q rho : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (muBig : (g : BG) → BP g → ℝ)
    (Knu : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (orientation k : ℤ)
    (x : FullPhysicalState SP smallMod BP bigMod (J + ell) cap)
    (out : FullPhysicalOutput SP smallMod BP bigMod (J + ell)) : ℂ :=
  ∑ z ∈ legalSourcePhysicalChoices SP smallMod BP bigMod
      J ell m cap patterns x orientation k,
    if sourcePhysicalOutput SP smallMod BP bigMod J ell m cap
        patterns x orientation k z = out then
      sourcePhysicalCoefficient SP smallMod BP bigMod J ell m cap
        patterns q rho Vsmall Vbig muBig Knu zeta theta
        orientation k x z
    else 0
/-- Source-wide global D/pattern disintegration into actual
physical output states, with no lost equal-output multiplicity. -/
theorem fullSourcePhysicalE_kernel_exact
    (q rho : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (muBig : (g : BG) → BP g → ℝ)
    (Knu : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (orientation k : ℤ)
    (x : FullPhysicalState SP smallMod BP bigMod (J + ell) cap)
    (F : FullPhysicalOutput SP smallMod BP bigMod (J + ell) → ℂ) :
    fullSourcePhysicalE SP smallMod BP bigMod J ell m cap
      patterns q rho Vsmall Vbig muBig Knu
      zeta theta orientation k x F =
    ∑ out ∈ fullSourcePhysicalSupport SP smallMod BP bigMod
        J ell m cap patterns x orientation k,
      fullSourcePhysicalKernel SP smallMod BP bigMod J ell m cap
        patterns q rho Vsmall Vbig muBig Knu
        zeta theta orientation k x out * F out := by
  unfold fullSourcePhysicalE fullSourcePhysicalSupport
    fullSourcePhysicalKernel
  classical
  rw [sum_over_exact_output_fibres
    (legalSourcePhysicalChoices SP smallMod BP bigMod
      J ell m cap patterns x orientation k)
    (sourcePhysicalOutput SP smallMod BP bigMod J ell m cap
      patterns x orientation k)
    (sourcePhysicalCoefficient SP smallMod BP bigMod J ell m cap
      patterns q rho Vsmall Vbig muBig Knu
      zeta theta orientation k x) F]
  apply Finset.sum_congr rfl
  intro out hout
  congr 1
  apply Finset.sum_congr rfl
  intro b hb
  split_ifs <;> rfl

end Green64FullPhysicalE

end

/-! ## PhysicalSourceOrientedFullE -/

section

open Classical
open scoped BigOperators

namespace Green64FullPhysicalE

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)]
variable [∀ g, DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ)
variable [∀ g, ∀ p, NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)]
variable [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ)
variable [∀ g, ∀ p, NeZero (bigMod g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu]
variable (patterns : Nu → SourcePattern BG J m)

/-- The FULL sampled physical edge exposes independent SMALL endpoint
permutations as well as independent BIG source and target ones.
Keeping small permutations explicit is essential: the original
divisor D contains the permuted SMALL shared prime labels. -/
abbrev FullOrientedBranch
    (x : FullPhysicalState SP smallMod BP bigMod (J + ell) cap) :=
  FullPhysicalEdgeBranch SP smallMod BP bigMod (J + ell) cap x ×
    Green64SmallHaar.GroupPermFamily (G := SG) (J + ell) ×
    Green64SmallHaar.GroupPermFamily (G := SG) (J + ell)

abbrev FullOrientedSourceChoice
    (x : FullPhysicalState SP smallMod BP bigMod (J + ell) cap) :=
  Σ nu : Nu,
    SourceBigAux BP J m (patterns nu) ×
      FullOrientedBranch SP smallMod BP bigMod J ell cap x

noncomputable instance
    (x : FullPhysicalState SP smallMod BP bigMod (J + ell) cap) :
    Fintype (FullOrientedSourceChoice SP smallMod BP bigMod
      J ell m cap patterns x) := inferInstance

/-- Source D as prescribed in TeX: ALL shared source labels in
the oriented SMALL and BIG endpoint lists, plus independent
BIG auxiliary free prime draws. Both sigma families enter D. -/
noncomputable def sourceOrientedPhysicalD
    (pat : SourcePattern BG J m)
    (aux : SourceBigAux BP J m pat)
    (x : FullPhysicalState SP smallMod BP bigMod (J + ell) cap)
    (bigSigma : BigGroupPerm (BG := BG) (J + ell))
    (smallSigma : Green64SmallHaar.GroupPermFamily (G := SG) (J + ell)) :
    ℕ :=
  (∏ g : SG, ∏ i ∈ sourceSmallShared J ell g,
    smallMod g (Green64SmallHaar.marks (smallMod g) (J + ell)
      (x.1 g) (smallSigma g i))) *
  (∏ g : BG,
    (∏ i ∈ sourceBigShared J ell m pat g,
      bigMod g ((x.2 g).1 (bigSigma g i))) *
    (∏ j : ↥(pat.free g), bigMod g (aux g j)))

noncomputable def sourceOrientedStep
    (pat : SourcePattern BG J m)
    (aux : SourceBigAux BP J m pat)
    (x : FullPhysicalState SP smallMod BP bigMod (J + ell) cap)
    (bigSigma : BigGroupPerm (BG := BG) (J + ell))
    (smallSigma : Green64SmallHaar.GroupPermFamily (G := SG) (J + ell))
    (orientation k : ℤ) : ℤ :=
  orientation * k * (sourceOrientedPhysicalD
    SP smallMod BP bigMod J ell m cap
    pat aux x bigSigma smallSigma : ℤ)

/-- Source-compliant physical E admissibility, BEFORE any aggregation:
oriented BIG shared slots, literal OLD stores/promotions and exclusions,
the TRUE small Haar congruence at the same dynamic step, and the
independent auxiliary ban. No global birth collision is imposed here. -/
def sourceOrientedPhysicalLegal
    (x : FullPhysicalState SP smallMod BP bigMod (J + ell) cap)
    (orientation k : ℤ)
    (z : FullOrientedSourceChoice SP smallMod BP bigMod
      J ell m cap patterns x) : Prop :=
  let pat := patterns z.1
  let aux := z.2.1
  let b := z.2.2.1
  let ss := z.2.2.2.1
  let tt := z.2.2.2.2
  let D := sourceOrientedPhysicalD SP smallMod BP bigMod
    J ell m cap pat aux x b.sigmaBig ss
  let step := sourceOrientedStep SP smallMod BP bigMod
    J ell m cap pat aux x b.sigmaBig ss orientation k
  (orientation = 1 ∨ orientation = -1) ∧ k ≠ 0 ∧
  sourceAuxAvoidsEndpoints SP smallMod BP bigMod
    J ell m cap pat aux x b ∧
  (∀ g : BG, OrientedBigEdgeLegal (bigMod g) (J + ell)
    (cap g) (x.2 g) (b.bigChoice g).1
    (sourceBigShared J ell m pat g)
    (b.sigmaBig g) (b.tauBig g) D step (b.bigChoice g).2) ∧
  Green64SmallHaar.groupEdgeAllowedPerm
    SP smallMod (J + ell)
    (sourceSmallShared J ell) step ss tt x.1 b.smallTarget

noncomputable def sourceOrientedPhysicalChoices
    (x : FullPhysicalState SP smallMod BP bigMod (J + ell) cap)
    (orientation k : ℤ) :
    Finset (FullOrientedSourceChoice SP smallMod BP bigMod
      J ell m cap patterns x) :=
  Finset.univ.filter
    (sourceOrientedPhysicalLegal SP smallMod BP bigMod
      J ell m cap patterns x orientation k)

/-- One literal original source E_i summand. BIG fresh target
sampling uses exactly pattern-unshared, nonpromoted oriented slots;
SMALL physical Haar validity is checked for the SAME D/Delta.
There is only one Kν D^(iζ) Fourier phase and both independent
endpoint permutation averages. The input Fock j! is not charged
again in this row. -/
noncomputable def sourceOrientedPhysicalCoefficient
    (q rho : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (muBig : (g : BG) → BP g → ℝ)
    (Knu : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (orientation k : ℤ)
    (x : FullPhysicalState SP smallMod BP bigMod (J + ell) cap)
    (z : FullOrientedSourceChoice SP smallMod BP bigMod
      J ell m cap patterns x) : ℂ :=
  let pat := patterns z.1
  let aux := z.2.1
  let b := z.2.2.1
  let ss := z.2.2.2.1
  let tt := z.2.2.2.2
  let D := sourceOrientedPhysicalD SP smallMod BP bigMod
    J ell m cap pat aux x b.sigmaBig ss
  let step := sourceOrientedStep SP smallMod BP bigMod
    J ell m cap pat aux x b.sigmaBig ss orientation k
  (sourceAuxMass BP bigMod J m Vbig pat aux : ℂ) *
    (bigEndpointPairMass (BG := BG) (J + ell) : ℂ) *
    (Green64SmallHaar.groupPermutationPairMass
      (G := SG) (J + ell) : ℂ) *
    (∏ g : BG, orientedBigBranchCoefficient
      (bigMod g) (J + ell) (cap g) (muBig g) (Vbig g) rho
      (x.2 g) (b.bigChoice g).1
      (sourceBigShared J ell m pat g)
      (b.sigmaBig g) (b.tauBig g) step (b.bigChoice g).2) *
    Green64SmallHaar.groupPermutedKernel
      SP smallMod (J + ell) q Vsmall
      (sourceSmallShared J ell) step
      (fun _ _ => originalEdgeScalar
        (Knu z.1 aux
          (fun g i => (x.2 g).1 (b.sigmaBig g i))
          (fun g i => (b.bigChoice g).1 (b.tauBig g i)))
        zeta theta D orientation k)
      ss tt x.1 b.smallTarget

noncomputable def sourceOrientedPhysicalOutput
    (x : FullPhysicalState SP smallMod BP bigMod (J + ell) cap)
    (orientation k : ℤ)
    (z : FullOrientedSourceChoice SP smallMod BP bigMod
      J ell m cap patterns x) :
    FullPhysicalOutput SP smallMod BP bigMod (J + ell) :=
  let b := z.2.2.1
  fullPhysicalBranchOutput SP smallMod BP bigMod
    (J + ell) cap x
    (sourceOrientedStep SP smallMod BP bigMod J ell m cap
      (patterns z.1) z.2.1 x b.sigmaBig z.2.2.2.1
      orientation k) b

/-- Finite physical E at the exact original oriented source
scope; OLD/promotion and memory states are physical, not a
postulated Markov law. -/
noncomputable def fullSourceOrientedPhysicalE
    (q rho : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (muBig : (g : BG) → BP g → ℝ)
    (Knu : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (orientation k : ℤ)
    (x : FullPhysicalState SP smallMod BP bigMod (J + ell) cap)
    (F : FullPhysicalOutput SP smallMod BP bigMod (J + ell) → ℂ) :
    ℂ :=
  ∑ z ∈ sourceOrientedPhysicalChoices SP smallMod BP bigMod
      J ell m cap patterns x orientation k,
    sourceOrientedPhysicalCoefficient SP smallMod BP bigMod
      J ell m cap patterns q rho Vsmall Vbig muBig Knu
      zeta theta orientation k x z *
    F (sourceOrientedPhysicalOutput SP smallMod BP bigMod
      J ell m cap patterns x orientation k z)

end Green64FullPhysicalE

end

/-! ## PhysicalOrientedDivisorAudit -/

section

open Classical
open scoped BigOperators

namespace Green64FullPhysicalE

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)]
variable [∀ g, DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ)
variable [∀ g, ∀ p, NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)]
variable [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ)
variable [∀ g, ∀ p, NeZero (bigMod g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)

/-- The actual BIG shared label AFTER sampling the source endpoint
permutation divides the dynamically sampled original source D.
This was not true for the unpermuted sourcePhysicalD when σ moves
a shared label. -/
theorem oriented_shared_big_prime_dvd_D
    (pat : SourcePattern BG J m)
    (aux : SourceBigAux BP J m pat)
    (x : FullPhysicalState SP smallMod BP bigMod (J + ell) cap)
    (sigma : BigGroupPerm (BG := BG) (J + ell))
    (ss : Green64SmallHaar.GroupPermFamily (G := SG) (J + ell))
    (g : BG) (i : Fin (J + ell))
    (hi : i ∈ sourceBigShared J ell m pat g) :
    bigMod g ((x.2 g).1 (sigma g i)) ∣
      sourceOrientedPhysicalD SP smallMod BP bigMod J ell m cap
        pat aux x sigma ss := by
  unfold sourceOrientedPhysicalD
  have hshared :
      bigMod g ((x.2 g).1 (sigma g i)) ∣
      (∏ j ∈ sourceBigShared J ell m pat g,
        bigMod g ((x.2 g).1 (sigma g j))) :=
    Finset.dvd_prod_of_mem (s := sourceBigShared J ell m pat g)
      (f := fun j => bigMod g ((x.2 g).1 (sigma g j))) hi
  have hgroup :
      bigMod g ((x.2 g).1 (sigma g i)) ∣
      (∏ j ∈ sourceBigShared J ell m pat g,
        bigMod g ((x.2 g).1 (sigma g j))) *
        (∏ j : ↥(pat.free g), bigMod g (aux g j)) :=
    dvd_mul_of_dvd_left hshared _
  have hgroups :
      bigMod g ((x.2 g).1 (sigma g i)) ∣
      (∏ gg : BG,
        (∏ j ∈ sourceBigShared J ell m pat gg,
          bigMod gg ((x.2 gg).1 (sigma gg j))) *
        (∏ j : ↥(pat.free gg), bigMod gg (aux gg j))) := by
    exact hgroup.trans (Finset.dvd_prod_of_mem
      (s := Finset.univ)
      (f := fun gg : BG =>
        (∏ j ∈ sourceBigShared J ell m pat gg,
          bigMod gg ((x.2 gg).1 (sigma gg j))) *
        (∏ j : ↥(pat.free gg), bigMod gg (aux gg j)))
      (Finset.mem_univ g))
  exact dvd_mul_of_dvd_right hgroups _

/-- The repaired divisor agrees with the previous source D
precisely at identity endpoint permutations. The disagreement
occurs when patterns are evaluated on independently oriented
lists, as required by the source symmetrizations. -/
theorem oriented_D_identity_permutations
    (pat : SourcePattern BG J m)
    (aux : SourceBigAux BP J m pat)
    (x : FullPhysicalState SP smallMod BP bigMod (J + ell) cap) :
    sourceOrientedPhysicalD SP smallMod BP bigMod J ell m cap
      pat aux x (fun _ => Equiv.refl _)
      (fun _ => Equiv.refl _) =
    sourcePhysicalD SP smallMod BP bigMod J ell m cap
      pat aux x := by
  simp [sourceOrientedPhysicalD, sourcePhysicalD]

end Green64FullPhysicalE

end

/-! ## PhysicalOrientedEdgeKernel -/

section

open Classical
open scoped BigOperators

namespace Green64FullPhysicalE

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)]
variable [∀ g, DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ)
variable [∀ g, ∀ p, NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)]
variable [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ)
variable [∀ g, ∀ p, NeZero (bigMod g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu]
variable (patterns : Nu → SourcePattern BG J m)

/-- The exact reachable output carrier for a complete oriented
physical E edge, after ALL choices of small/big permutations,
pattern, independent auxiliary D, stores, OLD injections, fresh
target integrals and source K, without deduplicating witnesses. -/
noncomputable def orientedEdgeSupport
    (x : FullPhysicalState SP smallMod BP bigMod (J + ell) cap)
    (orientation k : ℤ) :
    Finset (FullPhysicalOutput SP smallMod BP bigMod (J + ell)) :=
  (sourceOrientedPhysicalChoices SP smallMod BP bigMod
    J ell m cap patterns x orientation k).image
    (sourceOrientedPhysicalOutput SP smallMod BP bigMod
      J ell m cap patterns x orientation k)
noncomputable def orientedEdgeStateKernel
    (q rho : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (muBig : (g : BG) → BP g → ℝ)
    (Knu : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (orientation k : ℤ)
    (x : FullPhysicalState SP smallMod BP bigMod (J + ell) cap)
    (out : FullPhysicalOutput SP smallMod BP bigMod (J + ell)) : ℂ :=
  ∑ z ∈ sourceOrientedPhysicalChoices SP smallMod BP bigMod
      J ell m cap patterns x orientation k,
    if sourceOrientedPhysicalOutput SP smallMod BP bigMod
       J ell m cap patterns x orientation k z = out then
      sourceOrientedPhysicalCoefficient SP smallMod BP bigMod
        J ell m cap patterns q rho Vsmall Vbig muBig
        Knu zeta theta orientation k x z
    else 0

/-- No source witness multiplicity is discarded when passing from
the true orientation-corrected E_i branch sum to output multisets. -/
theorem fullSourceOrientedE_kernel_exact
    (q rho : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (muBig : (g : BG) → BP g → ℝ)
    (Knu : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (orientation k : ℤ)
    (x : FullPhysicalState SP smallMod BP bigMod (J + ell) cap)
    (F : FullPhysicalOutput SP smallMod BP bigMod (J + ell) → ℂ) :
    fullSourceOrientedPhysicalE SP smallMod BP bigMod
      J ell m cap patterns q rho Vsmall Vbig muBig
      Knu zeta theta orientation k x F =
    ∑ out ∈ orientedEdgeSupport SP smallMod BP bigMod
        J ell m cap patterns x orientation k,
      orientedEdgeStateKernel SP smallMod BP bigMod
        J ell m cap patterns q rho Vsmall Vbig muBig
        Knu zeta theta orientation k x out * F out := by
  classical
  unfold fullSourceOrientedPhysicalE orientedEdgeSupport orientedEdgeStateKernel
  rw [sum_over_exact_output_fibres
    (sourceOrientedPhysicalChoices SP smallMod BP bigMod
      J ell m cap patterns x orientation k)
    (sourceOrientedPhysicalOutput SP smallMod BP bigMod
      J ell m cap patterns x orientation k)
    (sourceOrientedPhysicalCoefficient SP smallMod BP bigMod
      J ell m cap patterns q rho Vsmall Vbig muBig
      Knu zeta theta orientation k x) F]
  apply Finset.sum_congr rfl
  intro out hout
  congr 1
  apply Finset.sum_congr rfl
  intro b hb
  split_ifs <;> rfl
end Green64FullPhysicalE

end

