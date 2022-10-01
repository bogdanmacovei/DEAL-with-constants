import logic.basic 

/-
  **Implementation of DEALc**
-/

variable σ : ℕ 

/-
  Inductive types for actions and formulas and notations
-/

inductive action : Type 
| skip : fin σ → action 
| seq : action → action → action 

notation `PDL∅` := action.skip 
notation act1 `;` act2 := action.seq act1 act2

inductive const : Type 
| const : fin σ -> const 
| encr : const -> const -> const 
| tupl : const -> const -> const 

inductive agent : Type 
| agent : fin σ -> agent 

inductive form : Type 
| atom : fin σ → form 
| const : const σ → form 
| bot : form 
| impl : form → form → form 
| k : form → form 
| b : form → form 
| pdl : form → action σ → form 

prefix `#` := form.atom 
notation `c` := form.const 
notation `⊥` := form.bot
infix `⊃` := form.impl 
notation `¬`:40 p := form.impl p (form.bot)
notation p `&` q := ¬(p ⊃ ¬q)
notation p `or` q := ¬(¬p & ¬q)
notation `K□`:80 p := form.k p 
notation `K◇`:80 := λ p, ¬(K□ (¬ p))
notation `B□`:80 p := form.b p 
notation `B◇`:80 := λ p, ¬(B□ (¬ p))
notation `PDL□`:80 := form.pdl

variables { p q : fin σ }
variables { act1 act2 : fin σ }
#check PDL□ (#p) (PDL∅ act1)

/-
  Context definition 
-/

@[reducible]
def ctx (σ : nat) : Type := set (form σ)

notation `·` := {}
notation Γ ` ∪ ` p := set.insert p Γ

#check · ∪ (#p)

/-
  Proof system 
-/

open form 
open action 

inductive Proof : ctx σ → form σ → Prop 
-- Propositional logic
| ax { Γ } { p } (h : p ∈ Γ) : Proof Γ p  
| pl1 { Γ } { p q } : Proof Γ (p ⊃ (q ⊃ p))
| pl2 { Γ } { p q r } : Proof Γ ((p ⊃ (q ⊃ r)) ⊃ ((p ⊃ q) ⊃ (p ⊃ r)))
| pl3 { Γ } { p q } : Proof Γ (((¬p) ⊃ ¬q) ⊃ (((¬p) ⊃ q) ⊃ p))
-- S5
| kk { Γ } { p q } : Proof Γ ((K□(p ⊃ q)) ⊃ (K□p ⊃ K□q))
| t { Γ } { p } : Proof Γ (K□p ⊃ p) 
| s4 { Γ } { p } : Proof Γ (K□p ⊃ K□K□p) 
| s5 { Γ } { p } : Proof Γ (¬(K□p) ⊃ K□(¬K□p)) 
-- KD
| bk { Γ } { p q } : Proof Γ (B□(p ⊃ q) ⊃ (B□p ⊃ B□q))
| dox { Γ } { p } : Proof Γ (B□p ⊃ B◇p)
| kb { Γ } { p } : Proof Γ (K□p ⊃ B□p)
-- PDL
| pdlk { Γ } { p q } (α : action σ) : Proof Γ (PDL□(p ⊃ q) α ⊃ (PDL□p α ⊃ PDL□q α))
-- Deductive rules 
| mp { Γ } { p q } (hpq : Proof Γ (p ⊃ q)) (hp : Proof Γ p) : Proof Γ q
| knec { Γ } { p } (h : Proof · p) : Proof Γ (K□p)
| bnec { Γ } { p } (h : Proof · p) : Proof Γ (B□p)
| gen { Γ } { p } (α : action σ) (h : Proof · p) : Proof Γ (PDL□p α)

notation Γ `-` σ ` ⊢κ ` p := Proof σ Γ p
notation Γ `-` σ ` ⊬κ ` p := Proof σ Γ p → false 

/-
  lemmas 
-/
 
open Proof 

variable { S : ctx σ }
#check  S-σ ⊢κ (#p)

lemma idd {σ : ℕ} { p : form σ } { Γ : ctx σ } : Γ-σ ⊢κ (p ⊃ p) := mp (mp (@pl2 σ Γ p (p ⊃ p) p) pl1) pl1

lemma cut {σ : ℕ} {Γ : ctx σ} {p q r : form σ} :
  (Γ-σ ⊢κ p ⊃ q) → (Γ-σ ⊢κ q ⊃ r) → (Γ-σ ⊢κ p ⊃ r) :=
λ hpq hqr, mp (mp pl2 (mp pl1 hqr)) hpq

lemma dne { σ : ℕ } {p : form σ} {Γ : ctx σ} :
  Γ-σ ⊢κ (¬¬p) ⊃ p :=
have h : Γ-σ ⊢κ (¬¬p) ⊃ ((¬p) ⊃ (¬p)) := mp pl1 idd,
mp (mp pl2 (cut pl1 pl3)) h

/-
  Deduction theorem 
-/
 
theorem deduction { σ : ℕ } { Γ : ctx σ } { p q : form σ } { α : action σ } : ((Γ ∪ p)-σ ⊢κ q) → (Γ-σ ⊢κ p ⊃ q) :=
begin 
  generalize eq : (Γ ∪ p) = Γ',
  intro h,
  induction h; subst eq, 
  {
    repeat {cases h_h},
    exact idd,
    {
      exact mp pl1 (ax h_h)
    }
  },
  { exact mp pl1 pl1 },
  { exact mp pl1 pl2 },
  { exact mp pl1 pl3 },
  { exact mp pl1 kk },
  { exact mp pl1 t },
  { exact mp pl1 s4 },
  { exact mp pl1 s5 },
  { exact mp pl1 bk },
  { exact mp pl1 dox },
  { exact mp pl1 kb },
  { exact mp pl1 (pdlk h_α) },
  { apply mp,
    { exact (mp pl2 (h_ih_hpq rfl)) },
    { exact h_ih_hp rfl }
  },
  { exact mp pl1 (knec h_h) },
  { exact mp pl1 (bnec h_h) },
  { exact mp pl1 (gen h_α h_h) }
end 

/-
  Basic Semantics
-/

open form classical 

@[reducible]
def world (σ : ℕ) := ctx σ 

/-
  Models
-/

structure model := 
  (worlds : set (world σ))
  (kaccess : world σ → world σ → bool)
  (baccess : world σ → world σ → bool)
  (pdlaccess : world σ → world σ → bool)
  (val : fin σ → world σ → bool)
  (valc : const σ -> world σ -> bool)
  (refl : ∀ w ∈ worlds, kaccess w w = tt)
  (symm : ∀ w ∈ worlds, ∀ v ∈ worlds, kaccess w v = tt → kaccess v w = tt)
  (trans : ∀ w ∈ worlds, ∀ v ∈ worlds, ∀ u ∈ worlds, kaccess w v = tt → kaccess v u = tt → kaccess w u = tt)
  (serial : ∀ w ∈ worlds, ∃ v ∈ worlds, baccess w v = tt)



local attribute [instance] prop_decidable 

noncomputable def forces_form { σ : ℕ } (M : model σ) : form σ → world σ → bool 
| (#p) := λ w, M.val p w 
| (c p) := λ w, M.valc p w 
| (⊥) := λ w, ff 
| (p ⊃ q) := λ w, (bnot (forces_form p w)) || (forces_form q w)
| (K□ p) := λ w, if (∀ v ∈ M.worlds, w ∈ M.worlds → M.kaccess w v = tt → forces_form p v = tt) then tt else ff 
| (B□ p) := λ w, if (∀ v ∈ M.worlds, w ∈ M.worlds → M.baccess w v = tt → forces_form p v = tt) then tt else ff
| (PDL□ p (α : action σ)) := λ w, if (∀ v ∈ M.worlds, w ∈ M.worlds → M.pdlaccess w v = tt → forces_form p v = tt) then tt else ff  

notation w `⊩` `⦃` M `⦄ ` p := forces_form M p w

noncomputable def forces_ctx { σ : ℕ } (M : model σ) (Γ : ctx σ) : world σ → bool := 
  λ w, if (∀ p, p ∈ Γ → forces_form M p w = tt) then tt else ff

notation w `⊩` `⦃` M `⦄ ` p := forces_ctx M p w

inductive sem_csq { σ : ℕ } (Γ : ctx σ) (p : form σ) : Prop
| is_true (m : ∀ (M : model σ) (w ∈ M.worlds), ((w ⊩ ⦃M⦄ Γ) = tt) → (w ⊩ ⦃M⦄ p) = tt) : sem_csq

notation Γ `-` σ ` ⊨κ ` p := @sem_csq σ Γ p

/-
  Some lemmas
-/

lemma ctx_tt_iff_mem_tt { σ : ℕ } {Γ : ctx σ} {M : model σ} {w : world σ} :
  (w ⊩⦃M⦄ Γ) = tt ↔ (∀ p, p ∈ Γ → (w ⊩⦃M⦄ p) = tt) := sorry 

lemma ctx_tt_to_mem_tt { σ : ℕ } {Γ : ctx σ} {M : model σ } {w : world σ} {p : form σ} :
  (w ⊩⦃M⦄ Γ) = tt → p ∈ Γ → (w ⊩⦃M⦄ p) = tt :=
by intro; apply ctx_tt_iff_mem_tt.1; assumption

axiom impl_iff_implies_v2 :
  ∀ (σ : ℕ) {M : model σ} {w : world σ} {p q : form σ},
    (λ (x_1 : world σ) (x_2 : model σ) (x_3 : form σ), x_1⊩⦃x_2⦄ x_3) w M (p⊃q) = tt ↔
      ↥((λ (x_1 : world σ) (x_2 : model σ) (x_3 : form σ), x_1⊩⦃x_2⦄ x_3) w M p) →
      ↥((λ (x_1 : world σ) (x_2 : model σ) (x_3 : form σ), x_1⊩⦃x_2⦄ x_3) w M q)

lemma impl_iff_implies {M : model σ } {w : world σ} {p q : form σ} :
  (w ⊩⦃M⦄ p ⊃ q) = tt ↔ ((w ⊩⦃M⦄ p) → (w ⊩⦃M⦄ q)) :=
by unfold forces_form; induction (forces_form M p w); repeat {induction (forces_form M q w), simp, simp}

lemma impl_tt_iff_ff_or_tt { σ : ℕ } {M : model σ } {w : world σ} {p q : form σ} :
  (w ⊩⦃M⦄ p ⊃ q) = tt ↔ ¬(w ⊩⦃M⦄ p) ∨ (w ⊩⦃M⦄ q) = tt :=
by unfold forces_form; induction (forces_form M p w); repeat {induction (forces_form M q w), simp, simp}

lemma ff_or_tt_and_tt_implies_tt_right { σ : ℕ } {M : model σ} {w : world σ} {p q : form σ} :
  (¬(w ⊩⦃M⦄ p) ∨ (w ⊩⦃M⦄ q) = tt) → (w ⊩⦃M⦄ p) = tt → (w ⊩⦃M⦄ q) = tt := sorry 
-- by simp; induction (forces_form M p w); repeat {induction (forces_form M q w), simp, simp}

lemma bot_is_insatisf { σ : ℕ }{w : world σ} : 
  ¬ ∃ (M : model σ ), (w ⊩⦃M⦄ ⊥) = tt :=
by intro h; cases h; exact (bool.no_confusion h_h) 

lemma is_true_pl1 { σ : ℕ }{M : model σ } {w : world σ} {p q : form σ} : 
  (w ⊩⦃M⦄ p ⊃ (q ⊃ p)) = tt := 
begin
  apply impl_iff_implies.2,
  intro, apply impl_iff_implies.2,
  intro, assumption
end

lemma is_true_pl2 { σ : ℕ } {M : model σ } {w : world σ} {p q r : form σ} : 
  (w ⊩⦃M⦄ (p ⊃ (q ⊃ r)) ⊃ ((p ⊃ q) ⊃ (p ⊃ r))) = tt := 
begin
  apply impl_iff_implies.2,
  intro h₁, apply impl_iff_implies.2,
  intro h₂, apply impl_iff_implies.2,
  intro h₃, apply impl_iff_implies.1 ((impl_iff_implies.1 h₁) h₃),
  apply impl_iff_implies.1 h₂, assumption
end

lemma is_true_pl3 { σ : ℕ } { M : model σ } {w : world σ} {p q : form σ} : 
  (w ⊩⦃M⦄ ((¬p) ⊃ ¬q) ⊃ (((¬p) ⊃ q) ⊃ p)) = tt := 
begin
  unfold forces_form,
  induction (forces_form M p w),
  repeat { induction (forces_form M q w), repeat {simp} },
end

lemma nec_impl_to_nec_to_nec { σ : ℕ } {M : model σ } {w : world σ} {p q : form σ} : 
  (w ⊩⦃M⦄ K□ (p ⊃ q)) = tt → (w ⊩⦃M⦄ K□p) = tt → (w ⊩⦃M⦄ K□q) = tt := sorry 
-- begin
--   unfold forces_form, simp at *, intros hlpq hlp v wmem vmem rwv,
--   apply ff_or_tt_and_tt_implies_tt_right, 
--     rw or.comm, simp, apply hlpq, repeat {assumption}, 
--     apply hlp, repeat {assumption}, 
-- end

lemma knec_impl_to_knec_impl_knec { σ : ℕ } {M : model σ } {w : world σ} {p q : form σ} : 
  (w ⊩⦃M⦄ K□(p ⊃ q)) = tt → (¬(w ⊩⦃M⦄ K□p) ∨ (w ⊩⦃M⦄ K□q) = tt) := sorry

lemma bnec_impl_to_bnec_impl_bnec  { σ : ℕ } {M : model σ } {w : world σ} {p q : form σ} : 
  (w ⊩⦃M⦄ B□(p ⊃ q)) = tt → (¬(w ⊩⦃M⦄ B□p) ∨ (w ⊩⦃M⦄ B□q) = tt) := sorry

lemma gen_impl_to_gen_impl_gen  { σ : ℕ } {M : model σ } {w : world σ} { α : action σ } {p q : form σ} : 
  (w ⊩⦃M⦄ PDL□(p ⊃ q) α) = tt → (¬(w ⊩⦃M⦄ PDL□ p α) ∨ (w ⊩⦃M⦄ PDL□ q α) = tt) := sorry

lemma is_true_kk { σ : ℕ } {M : model σ} {w : world σ} {p q : form σ} : 
  (w⊩⦃M⦄ (K□p⊃q)⊃K□p⊃K□q) = tt := 
impl_iff_implies_v2 (λ h, impl_tt_iff_ff_or_tt.2 (knec_impl_to_knec_impl_knec h))

axiom is_true_dox { σ : ℕ } { M : model σ } { w : world σ } { p q : form σ } : 
  (w⊩⦃M⦄ B□p⊃¬B□¬p) = tt 

axiom is_true_kb {σ : ℕ} {M : model σ } {w : world σ} {p q : form σ} : 
  (w⊩⦃M⦄ B□(p⊃q)⊃(B□p⊃B□q)) = tt 

axiom is_true_kpdl {σ : ℕ} {M : model σ } {w : world σ} {α : action σ} {p q : form σ} : 
  (w ⊩⦃M⦄ (PDL□(p ⊃ q) α) ⊃ ((PDL□ p α) ⊃ PDL□ q α)) = tt 

lemma nec_to_tt {σ : ℕ} {M : model σ } {w : world σ} {wm : w ∈ M.worlds} {p : form σ} :
  (w ⊩⦃M⦄ K□p) = tt → (w ⊩⦃M⦄ p) = tt := 
begin
  unfold forces_form, simp at *,
  intro f, apply f, repeat {assumption},
  apply M.refl, assumption
end

axiom K_implies_B {σ: ℕ}
(M: model σ) (w: world σ) (wm: w ∈ M.worlds)
(p: form σ) (f₁: world σ) (f₂: f₁ ∈ M.worlds)
(f₃: w ∈ M.worlds) (f₄: M.kaccess w f₁ = tt) : (f₁⊩⦃M⦄ p) = ff ∨ ∀ (v : world σ), v ∈ M.worlds → f₁ ∈ M.worlds → M.baccess f₁ v = tt → (v⊩⦃M⦄ p) = tt

lemma is_true_kd { σ : ℕ } { M : model σ } { w : world σ } { wm : w ∈ M.worlds } { p : form σ } : 
  (w⊩⦃M⦄ K□p⊃B□p) = tt := 
begin 
  unfold forces_form,
  simp at *,
  intros f₁ f₂ f₃ f₄,
  exact K_implies_B M w wm p f₁ f₂ f₃ f₄ 
end 

axiom is_true_t {σ : ℕ} {M : model σ} {w : world σ} {w ∈ M.worlds} {p : form σ} : 
  (w⊩⦃M⦄ K□p⊃p) = tt 

lemma nec_to_nec_of_nec {σ : ℕ} {M : model σ} {w : world σ} {p : form σ} : 
  (w ⊩⦃M⦄ K□p) = tt → (w ⊩⦃M⦄ K□K□p) = tt := 
begin
  unfold forces_form, simp at *,
  intros f v wmem vmem rwv u vmem' umem rvu,
  apply f, repeat {assumption},
  refine M.trans _ _ _ _ _ _ rwv rvu,
  repeat {assumption}
end

axiom neg_nec_to_neg_of_neg_nec_helper {σ : ℕ}
(M: model σ) (w: world σ) (p: form σ)
(f: ¬∀ (v : world σ), v ∈ M.worlds → w ∈ M.worlds → M.kaccess w v = tt → (v⊩⦃M⦄ p) = tt)
(v: world σ) (vmem: v ∈ M.worlds) (wmem: w ∈ M.worlds)
(rwv: M.kaccess w v = tt) (u: ∀ (v_1 : world σ), v_1 ∈ M.worlds → v ∈ M.worlds → M.kaccess v v_1 = tt → (v_1⊩⦃M⦄ p) = tt) 
: ∀ (v : world σ), v ∈ M.worlds → w ∈ M.worlds → M.kaccess w v = tt → (v⊩⦃M⦄ p) = tt

lemma neg_nec_to_neg_of_neg_nec { σ : ℕ } { M : model σ } { w : world σ } { p : form σ } : 
  (w ⊩ ⦃M⦄ ¬K□p) = tt → (w ⊩ ⦃M⦄ K□(¬K□p)) = tt :=
begin 
  unfold forces_form, simp at *,
  intros f v vmem wmem rwv u,
  apply f, 
  repeat {assumption},
  apply neg_nec_to_neg_of_neg_nec_helper M w p f v vmem wmem rwv,
  sorry 
end 


axiom is_true_s4 {σ : ℕ} {M : model σ} {w : world σ} {p : form σ} : 
  (w⊩⦃M⦄ K□p⊃K□K□p) = tt 

axiom is_true_s5 {σ : ℕ} {M : model σ} {w : world σ} {p : form σ} : 
  (w ⊩⦃M⦄ ¬(K□p) ⊃ K□(¬K□p)) = tt 

axiom empty_ctx_tt {σ : ℕ } {M : model σ } {w : world σ} : 
  (w ⊩⦃M⦄ ·) = tt  

/-
  Soundness
-/

theorem soundness { σ : ℕ } { Γ : ctx σ } { p : form σ } : (Γ-σ ⊢κ p) → (Γ-σ ⊨κ p) := 
begin 
  intro h,
  induction h,
  {
    apply sem_csq.is_true,
    intros,
    apply ctx_tt_to_mem_tt,
    repeat { assumption }
  }, 
  {
    apply sem_csq.is_true,
    intros M w wmem ctt,
    apply is_true_pl1 
  },
  {
    apply sem_csq.is_true,
    intros M w wmem ctt,
    apply is_true_pl2 
  },
  {
    apply sem_csq.is_true,
    intros M w wmem ctt,
    apply is_true_pl3 
  },
  { apply sem_csq.is_true,
    intros M w wmem ctt, 
    apply is_true_kk 
  },
  { apply sem_csq.is_true,
    intros M w wmem ctt,
    apply is_true_t,
    repeat {assumption}
  },
  { apply sem_csq.is_true,
    intros M w wmem ctt,
    apply is_true_s4
  },
  {
    apply sem_csq.is_true,
    intros M w wmem ctt,
    apply is_true_s5 
  },
  {
    apply sem_csq.is_true,
    intros M w wmem ctt,
    apply is_true_kb
  },
  {
    apply sem_csq.is_true,
    intros M w wmem ctt,
    apply is_true_dox,
    repeat { assumption }
  },
  {
    apply sem_csq.is_true,
    intros M w wmem ctt,
    apply is_true_kd,
    repeat { assumption }
  },
  {
    apply sem_csq.is_true,
    intros M w wmem ctt,
    apply is_true_kpdl  
  },
  { apply sem_csq.is_true,
    induction h_ih_hpq,
    induction h_ih_hp,
    intros M w wmem ctt,
    revert h_ih_hpq,
    unfold forces_form, simp,
    intro hpq,
    cases (hpq M w wmem ctt),
    { assumption },
    { exfalso,
      apply tt_eq_ff_eq_false,
      rw eq.symm (h_ih_hp M w wmem ctt),
      assumption 
    } 
  },
  { 
    apply sem_csq.is_true,
    intros M w wmem ctt,
    unfold forces_form, simp,
    induction h_ih,
    intros v vmem wmem rwv,
    apply h_ih, assumption,
    apply empty_ctx_tt 
  },
  { apply sem_csq.is_true,
    intros M w wmem ctt,
    unfold forces_form, simp,
    induction h_ih,
    intros v vmem wmem rwv,
    apply h_ih, assumption,
    apply empty_ctx_tt 
  },
  { apply sem_csq.is_true,
    intros M w wmem ctt,
    unfold forces_form, simp,
    induction h_ih,
    intros v vmem wmem rwv,
    apply h_ih, assumption,
    apply empty_ctx_tt 
  }
end 

/-
  Completeness
-/

open nat set classical

local attribute [instance, priority 0] prop_decidable

def is_consist { σ : ℕ } (Γ : ctx σ) := Γ-σ ⊬κ ⊥

def is_max (Γ : ctx σ) := is_consist Γ ∧ ∀ p, p ∈ Γ ∨ (¬p) ∈ Γ

def insert_form (Γ : ctx σ) (p : form σ) : ctx σ :=
  if is_consist (Γ ∪ p) then Γ ∪ p else Γ ∪ ¬p

def canonical_const {Γ : ctx σ} (c₀ : const σ) := ⋃ Γ, is_max Γ ∧ c₀ ∈ Γ 
def insert_code (Γ : ctx σ) (n : nat) : ctx σ :=
match encodable.decode (form σ) n with
| none := Γ
| some p := insert_form Γ p
end

@[simp]
def maxn (Γ : ctx σ) : nat → ctx σ
| 0     := Γ
| (n+1) := insert_code (maxn n) n

@[simp]
def max (Γ : ctx σ) : ctx σ := ⋃ n, maxn Γ n

lemma consist_not_of_not_prf { σ : ℕ } {Γ : ctx σ} {p : form σ} :
  (Γ-σ ⊬κ  p) → is_consist (Γ ∪ ¬p) :=
λ hnp hc, hnp (mp dne (deduction hc))

axiom not_imp_not : ∀ {a b : Prop} [_inst_1 : decidable a], ¬a → ¬b ↔ b → a

theorem completeness { σ : ℕ }{ Γ : ctx σ} {p : form σ} : 
  (Γ-σ ⊨κ p) → (Γ-σ ⊢κ  p) :=
begin
  apply (@not_imp_not (Γ-σ ⊢κ p) (Γ-σ ⊨κ  p) (prop_decidable _)).1,
  intros nhp hp, cases hp,
  have : is_consist (Γ ∪ ¬p) := consist_not_of_not_prf nhp,
  apply absurd,
  fapply hp,
    { exact model σ },
    { apply mem_domain c },
    { exact ctx.max (Γ ∪ ¬p) },
    { apply cons_ctx_tt_to_ctx_tt,
      apply ctx_tt_to_subctx_tt,
      apply ctx_tt_of_mem_domain (ctx.max (Γ ∪ ¬p)),
      apply mem_domain c,
      apply ctx.subset_max_self },

    { simp, apply eq_ff_of_not_eq_tt,
      apply neg_tt_iff_ff.1, 
      apply and.elim_right,
      apply cons_ctx_tt_iff_and.1, 
      apply ctx_tt_to_subctx_tt,
      apply ctx_tt_of_mem_domain (ctx.max (Γ ∪ ¬p)),
      apply mem_domain c,
      apply ctx.subset_max_self },
end