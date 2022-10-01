-- language -- 
inductive message (σ : ℕ) : Type 
  | null : fin σ -> message 
  | conc : message -> message -> message 
  | nonc : message -> message 
  | pk : message -> message
  | sk : message -> message 
  | keys : message -> message -> message -> message 
  | encr : message -> message -> message
  | decr : message -> message -> message
  | tupl : message -> message -> message 
  | func : message -> message -> message 

inductive program (σ : ℕ) : Type 
  | skip : program 
  | secv : program -> program -> program 
  | reun : program -> program -> program 
  | send : program 
  | recv : program 
  | agP : program -> message σ -> message σ -> program 

inductive form (σ : ℕ) : Type 
  | atom : fin σ -> form 
  | botm : form 
  | impl : form -> form -> form 
  | k : message σ -> form -> form 
  | b : message σ -> form -> form 
  | pdl : program σ -> message σ → message σ → form -> form 
  | toP : program σ -> form -> form 
  | mesg : message σ -> form 

prefix `#` := form.atom 
notation `⊥` := form.botm
infix `⊃` := form.impl 
notation `~`:40 p := form.impl p ⊥ 
notation p `&` q := ~(p ⊃ ~q)
notation p `or` q := ~(~p & ~q)
notation `K□`:80 m `,` p := form.k m p 
notation `B□`:80 m `,` p := form.b m p 
notation `[` α ` : ` i ` , ` j ` ] `:80  p := form.pdl α i j p 
notation `[` α `]`:80 p := form.toP α p 
notation `c` m := form.mesg m 
notation `[` α ` : ` i ` & ` j ` ] `:80  p := program.agP α i j
notation α `;` β := program.secv α β 

@[reducible]
def ctx (σ : nat) : Type := set (form σ)

notation `·` := {}
notation Γ ` ∪ ` p := set.insert p Γ

set_option trace.eqn_compiler.elim_match true

/-
  Proof system 
-/

open form 
open message
open program 

inductive Proof { σ : ℕ } : ctx σ → form σ → Prop 
-- Propositional logic
| ax { Γ } { p : form σ } (h : p ∈ Γ) : Proof Γ p  
| pl1 { Γ } { p q : form σ } : Proof Γ (p ⊃ (q ⊃ p))
| pl2 { Γ } { p q r : form σ } : Proof Γ ((p ⊃ (q ⊃ r)) ⊃ ((p ⊃ q) ⊃ (p ⊃ r)))
| pl3 { Γ } { p q } : Proof Γ (((~p) ⊃ ~q) ⊃ (((~p) ⊃ q) ⊃ p))
-- S5
| kk { Γ } { i : message σ } { p q } : Proof Γ (K□ i, (p ⊃ q) ⊃ (K□ i, p ⊃ K□ i, q))
| t { Γ } { i : message σ } { p } : Proof Γ ((K□ i, p) ⊃ p) 
| s4 { Γ } { i : message σ } { p } : Proof Γ (K□ i, p ⊃ K□ i, K□ i, p) 
-- KD
| bk { Γ } { i : message σ } { p q } : Proof Γ ((B□ i, (p ⊃ q)) ⊃ ((B□ i, p) ⊃ (B□ i, q)))
| dox { Γ } { i : message σ } { p } : Proof Γ (B□ i, p ⊃ ~B□ i, (~p))
| kb { Γ } { i : message σ } { p } : Proof Γ ((K□ i, p) ⊃ (B□ i, p))
-- PDL
| pdlk { Γ } { i j : message σ } { p q } (α : program σ) : Proof Γ (([α : i, j](p ⊃ q)) ⊃ ([α : i, j]p  ⊃ [α : i, j] q))
| pdt { Γ } { i j : message σ } { p : form σ } {α : program σ } : Proof Γ (([α : i, j] p) ⊃ p)
-- Deductive rules 
| mp { Γ } { p q } (hpq: Proof Γ (p ⊃ q)) (hp : Proof Γ p) : Proof Γ q
| knec { Γ } { i : message σ } { p } (h : Proof · p) : Proof Γ (K□ i, p)
| bnec { Γ } { p } { i : message σ } (h : Proof · p) : Proof Γ (B□ i, p)
| gen { Γ } { p } { i j : message σ } (α : program σ) (h : Proof Γ p) : Proof Γ ([α : i, j]p)
-- Protocols 
| h00 { Γ } { p : form σ } { i j : message σ } 
    (hsend : Proof Γ [send : i , j] p) 
    : Proof Γ [recv : j, i] p 
| h01 { Γ } { p : form σ } { i j : message σ } 
    (hsend : Proof Γ [recv : i , j] p) 
    : Proof Γ [send : j, i] p 
| h1 { Γ } { p : form σ } { i j : message σ } { α : program σ } 
    (ha : Proof Γ [α : i, j]p) 
    : Proof Γ (K□ i, p) 
| sk1 { Γ } { p : form σ } { k i j : message σ } 
    (h₀ : Proof Γ $ K□ i, (c k.keys i j)) 
    (h₁ : Proof Γ $ [recv : i, j]p) 
    : Proof Γ $ K□ i, K□ j, c k.keys i j 
| sk2 { Γ } { k i j Server : message σ }
    (h₀ : Proof Γ $ K□ i, c k)
    (h₁ : Proof Γ $ K□ j, c k)
    (h₂ : Proof Γ $ K□ Server, c k)
    : Proof Γ $ c k.keys i j 
| c1 { Γ } { m₁ m₂ : message σ }
    (h₀ : Proof Γ $ c m₁)
    (h₁ : Proof Γ $ c m₂)
    : Proof Γ $ c (m₁.tupl m₂)
| c2 { Γ } { m₁ m₂ : message σ }
    (h₀ : Proof Γ $ c m₁.tupl m₂)
    : Proof Γ $ c m₁
| c₂ { Γ } { t k : message σ } (h₁ : Proof Γ $ c t.encr k) (h₂ : Proof Γ $ c k) : Proof Γ $ c t 
| c3 { Γ } { m₁ m₂ : message σ }
    (h₀ : Proof Γ $ c m₁.tupl m₂)
    : Proof Γ $ c m₂
| c4 { Γ } { k i j : message σ }
    (h₀ : Proof Γ $ c k.keys i j)
    : Proof Γ $ c k.keys j i 
| c5 { Γ } { i m : message σ }
    (h₀ : Proof Γ $ K□i, c m.encr (i.pk))
    (h₁ : Proof Γ $ K□i, c (i.sk)) 
    : Proof Γ $ K□i, c m 
| c6 { Γ } { i m : message σ }
    (h₀ : Proof Γ $ K□i, c m.encr (i.sk))
    (h₁ : Proof Γ $ K□i, c (i.pk)) 
    : Proof Γ $ K□i, c m 


notation Γ ` ⊢κ ` p := Proof Γ p
notation Γ ` ⊬ ` p := Proof Γ p → false 

variable σ : ℕ 
variables { A B S : message σ }
variables { Na Nb Kab Kas Kbs : message σ }
variable Γ : ctx σ 
variable α : program σ 

open Proof 

/-
OSS - One Sided Secrecy
-/

axiom OSS_A_init_knowledge_0 : Γ ⊢κ K□ A, c Na 
axiom OSS_A_init_knowledge_1 : Γ ⊢κ K□ A, c Kab 
axiom OSS_B_init_knowledge_0 : Γ ⊢κ K□ B, c Kab 

axiom OSS_A_to_B : Γ ⊢κ [send : A, B] c Na.encr Kab 

theorem OSS_B_knows_Na : ∅ ⊢κ K□ B, c Na :=
    knec $ c₂ (mp t $ h1 $ h00 $ @OSS_A_to_B σ A B Na Kab ∅) 
    (mp t $ @OSS_B_init_knowledge_0 σ B Kab ∅)

/-
NSSK - Needham-Schroeder Secret-Key 
-/


variables { I R Ni Nr Kir Kis Krs : message σ }

axiom IK_I_0 : Γ ⊢κ K□ I, c Ni 
axiom IK_I_1 : Γ ⊢κ K□ I, c Kis 
axiom IK_R_0 : Γ ⊢κ K□ R, c Nr 
axiom IK_R_1 : Γ ⊢κ K□ R, c Krs 

def φIK := (K□ I, c Ni) & (K□ I, c Kis) 
  & (K□ R, c Nr) & (K□ R, c Krs) 

axiom NSSK_first : Γ ⊢κ ([send : I, S]c Ni)

axiom NSSK0 { α : program σ } : Γ ⊢κ [α](@φIK σ I R Ni Nr Kis Krs) ⊃ (@φIK σ I R Ni Nr Kis Krs)
axiom NSSK1 : (Γ ⊢κ [send : I, S] c Ni) -> (Γ ⊢κ c (Ni.tupl ((Kir).encr Krs)).encr Krs)
axiom NSSK2 : (Γ ⊢κ [send : S, I] (c (Ni.tupl ((Kir).encr Krs)).encr Krs)) -> (Γ ⊢κ c Kir.encr Krs)
axiom NSSK3 : (Γ ⊢κ [send : I, R] c Kir.encr Krs) -> (Γ ⊢κ c Nr.encr Kir)
axiom NSSK4 : (Γ ⊢κ [send : R, I] c Nr.encr Kir) -> (Γ ⊢κ c Nr.encr Kir)
axiom NSSK5 : Γ ⊢κ [send : I, R] (c Nr.encr Kir)

def φNSSK := [send : I, R][send : R, I][send : I, R][send : S, I][send : I, S]c Ni 

lemma I_knows_KiKr_key { I S Krs : message σ }
 (h₁ : Γ ⊢κ (@φNSSK σ S I R Ni))
 (h₂ : Γ ⊢κ (@φIK σ I R Ni Nr Kis Krs))
 :  Γ ⊢κ  K□ I, K□ R, c Kir.keys I R :=
begin 
  have h : (Γ ⊢κ ([send : I, S] c Ni)) := NSSK_first σ Γ, 
  have h₃ : (Γ ⊢κ [send : S, I] (c (Ni.tupl ((Kir).encr Krs)).encr Krs)) := gen send ((@NSSK1 σ S Γ I Ni Kir Krs) h),
  have h₄ : (Γ ⊢κ K□ I, c (Kir.keys I R)) := sorry,
  have h₅ : (Γ ⊢κ [send : I, R]c Kir.encr Krs) := gen send ((@NSSK2 σ S Γ I Ni Kir Krs) h₃),
  have h₆ : (Γ ⊢κ [send : R, I](c Nr.encr Kir)) := gen send ((@NSSK3 σ Γ I R Nr Kir Krs) h₅),
  have h₇ := h00 h₆,
  exact sk1 h₄ h₇ 
end 

/-
NSPK - Needham-Schroeder Public Key
-/

variables { eve ni nr : message σ }

axiom i_init₀ : Γ ⊢κ K□ I, c I.pk 
axiom i_init₁ : Γ ⊢κ K□ I, c I.sk 
axiom i_init₂ : Γ ⊢κ K□ I, c R.pk
axiom i_init₃ : Γ ⊢κ K□ I, c ni 

def ψNSPK := (K□ I, c I.pk) & (K□ I, c I.sk) & (K□ I, c R.pk) & (K□ I, c ni) 
  & (K□ R, c R.pk) & (K□ R, c R.sk) & (K□ R, c I.pk) & (K□ R, c nr)

axiom j_init₀ : Γ ⊢κ K□ R, c R.pk
axiom j_init₁ : Γ ⊢κ K□ R, c R.sk 
axiom j_init₂ : Γ ⊢κ K□ R, c I.pk
axiom j_init₃ : Γ ⊢κ K□ R, c nr 
axiom j_init₄ : Γ ⊢κ B□ R, [send : I, R] c ni 

axiom eve_init₀ : Γ ⊢κ K□ eve, c (I.pk) 
axiom eve_init₁ : Γ ⊢κ K□ eve, c (R.pk) 

axiom i_to_eve₀ : Γ ⊢κ [send : I, eve] c ni.encr (R.pk) 
axiom eve_to_j₀ : Γ ⊢κ [send : eve, R] c ni.encr (R.pk) 

axiom j_to_eve₁ : Γ ⊢κ [send : R, eve] c (ni.tupl nr).encr (I.pk) 
axiom eve_to_i₁ : Γ ⊢κ [send : R, eve] c (ni.tupl nr).encr (I.pk) 

axiom i_to_eve₂ : Γ ⊢κ [send : I, eve] c nr.encr (R.pk)
axiom eve_to_j₂ : Γ ⊢κ [send : eve, R] c nr.encr (R.pk) 


theorem NSAttacker : (Γ ⊢κ B□ R, [send : I, R] c ni) 
  ∧ (Γ ⊢κ [send : eve, R] c ni) :=
begin 
  apply and.intro, 
  {
    exact j_init₄ σ Γ
  },
  {
    have h₀ := mp (@pdt σ Γ eve j (c nj.encr (j.pk)) send) eve_to_j₂,
    have h₁ := @c₂ σ Γ j nj j h₀ (mp (@t σ Γ j (c j.sk)) (@j_init₁ σ Γ j)), 
    exact gen h₁
  }
end

/-
BAN - Burrows-Abadi-Needham Logic
-/

axiom tuple_π₁ { m m' : message σ } : (m.tupl m') = m 
axiom tuple_π₂ { m m' : message σ } : (m.tupl m') = m' 

axiom belief_over_conjunction {σ : ℕ} {Γ : ctx σ} { φ ψ : form σ } { A : message σ } :
  (Γ ⊢κ B□ A, φ) → (Γ ⊢κ B□ A, ψ) → (Γ ⊢κ B□ A, (φ & ψ))

lemma BAN_MMSK { A B m Kab : message σ } 
  (h₁ : ∅ ⊢κ K□ A, c Kab.keys A B)
  (h₂ : ∅ ⊢κ [recv : A, B] c m.encr Kab) :
    ∅ ⊢κ B□ A, [send : B, A] c m := 
  begin 
    have h₃ := mp kb h₁,
    have h₄ := mp pdt h₂,
    have h₅ := @bnec σ ∅ (c m.encr Kab) A h₄,
    have h₆ := h01 h₂,
    clear h₁ h₂ h₄,
    have h₇ := belief_over_conjunction h₃ h₅,
    have h₈ : (∅ ⊢κ B□ A, c m),
    have h₉ : (∅ ⊢κ [send : B , A ] c m), 
    exact bnec h₉
  end 
  
theorem BAN_JR { A B m Kab : message σ }
  (h₁ : Γ ⊢κ B□ A, ((B□ B, c m) ⊃ (c m)))
  (h₂ : Γ ⊢κ B□ A, (B□ B, c m)) 
    : Γ ⊢κ B□ A, c m := mp (mp (@bk σ Γ A ((B□ B, c m)) (c m)) h₁) h₂ 

theorem BAN_BC { i j m m' : message σ } 
  (h₁ : Γ ⊢κ B□ i, [send : j, i] c m.tupl m') 
    : Γ ⊢κ B□ i, [send : j, i] c m := 
  begin 
    rw [tuple_π₁] at h₁,
    exact h₁ 
  end 

theorem BAN_SC₁ { i j m m' : message σ } 
  (h : Γ ⊢κ [recv : i, j] (c m.tupl m')) 
  : Γ ⊢κ [recv : i, j] c m :=
  begin 
    rw [tuple_π₁] at h,
    exact h
  end 
 
theorem BAN_SC₂ { i j m m' : message σ } 
  (h : Γ ⊢κ [recv : i, j] (c m.tupl m')) 
  : Γ ⊢κ [recv : i, j] c m' :=
  begin 
    rw [tuple_π₂] at h,
    exact h
  end 