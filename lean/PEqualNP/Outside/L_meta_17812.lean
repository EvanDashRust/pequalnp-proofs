import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_17812

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def rwIdx (k w : ℕ) : ℕ := if w < k then w+2 else 0
def isAnd : GateOp → Bool
  | .and => true
  | _ => false
def getPin (k : ℕ) (a : Bool) (v : Option ℕ) : ℕ :=
  v.elim (if a then 1 else 0) (rwIdx k)
def encode (k : ℕ) (g : Gate) : Bool × ℕ × ℕ :=
  (isAnd g.op, getPin k (isAnd g.op) g.inputs[0]?, getPin k (isAnd g.op) g.inputs[1]?)
def encRun (k : ℕ) : List Gate → List (Bool × ℕ × ℕ)
  | [] => []
  | g :: gs => encode k g :: encRun (k+1) gs
def step (w : List Bool) (g : Bool × ℕ × ℕ) : List Bool :=
  w ++ [if g.1 then w.getD g.2.1 false && w.getD g.2.2 false
    else w.getD g.2.1 false || w.getD g.2.2 false]
def original (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem get_shift (w : List Bool) (j : ℕ) :
    (false :: true :: w).getD (rwIdx w.length j) false = w.getD j false := by
  unfold rwIdx
  split
  · rfl
  · have h : w.getD j false = false := List.getD_eq_default _ _ (by omega)
    rw [h]; rfl

theorem get_shift_opt (w : List Bool) (j : ℕ) :
    ((false :: true :: w)[rwIdx w.length j]?).getD false = (w[j]?).getD false := by
  simpa only [List.getD_eq_getElem?_getD] using get_shift w j

theorem step_encode (w : List Bool) (g : Gate)
    (h : (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) :
    step (false :: true :: w) (encode w.length g) = false :: true :: original w g := by
  obtain ⟨a,b⟩ := g
  rcases h.1 with hh | hh <;> change a = _ at hh <;> subst a
  all_goals
    rcases b with _ | ⟨p, _ | ⟨q, _ | ⟨r, s⟩⟩⟩
    · rfl
    · simp [step, original, encode, getPin, isAnd, GateOp.eval, get_shift_opt]
    · simp [step, original, encode, getPin, isAnd, GateOp.eval, get_shift_opt]
    · have hlen := h.2
      simp at hlen

theorem preserves (gs : List Gate) (w : List Bool)
    (h : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) :
    (encRun w.length gs).foldl step (false :: true :: w) =
      false :: true :: gs.foldl original w := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [encRun,List.foldl_cons]
    rw [step_encode w g (h g (List.mem_cons_self))]
    have hl : (original w g).length = w.length + 1 := by simp [original]
    rw [← hl]
    exact ih _ (fun t ht => h t (List.mem_cons_of_mem _ ht))

theorem len (k : ℕ) (gs : List Gate) : (encRun k gs).length = gs.length := by
  induction gs generalizing k with
  | nil => rfl
  | cons g gs ih => simp [encRun, ih]
theorem tapes (w : List Bool) (gs : List Gate) :
    (gs.foldl original w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih => simp [ih, original]; omega
theorem idx_bound (k w : ℕ) : rwIdx k w < k+2 := by
  unfold rwIdx
  split <;> omega
theorem pin_bound (k : ℕ) (b : Bool) (o : Option ℕ) : getPin k b o < k+2 := by
  cases o with
  | none => cases b <;> simp [getPin]
  | some j => exact idx_bound k j

theorem earlier (gs : List Gate) (k i : ℕ) (v : Bool × ℕ × ℕ)
    (h : (encRun k gs)[i]? = some v) : v.2.1 < k+i+2 ∧ v.2.2 < k+i+2 := by
  induction gs generalizing k i with
  | nil => simp [encRun] at h
  | cons g gs ih =>
    cases i with
    | zero =>
      simp [encRun] at h
      subst v
      exact ⟨pin_bound _ _ _,pin_bound _ _ _⟩
    | succ i =>
      simp [encRun] at h
      have he := ih (k+1) i h
      omega
end PEqualNP.Outside.L_meta_17812

open PEqualNP.Outside.L_meta_17812 in
theorem PEqualNP.Outside.L_meta_17812 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.Monotone2 x1 →     x1.size ≤ (18 : ℕ) →       ∃ (x4 : List (Bool × ℕ × ℕ)) (x5 : ℕ),         x4.length ≤ (18 : ℕ) ∧           x5 < (13 : ℕ) + x4.length ∧             (∀ (x6 : ℕ) (x7 : Bool × ℕ × ℕ), x4[x6]? = Option.some x7 → x7.2.1 < (13 : ℕ) + x6 ∧ x7.2.2 < (13 : ℕ) + x6) ∧               ∀ (x6 : List Bool),                 x6.length = (11 : ℕ) →                   (List.foldl                           (fun (x8 : List Bool) (x9 : Bool × ℕ × ℕ) =>                             have x10 : Bool := x8.getD x9.2.1 Bool.false;                             have x11 : Bool := x8.getD x9.2.2 Bool.false;                             x8 ++ [if x9.1 = Bool.true then x10 && x11 else x10 || x11])                           (Bool.false :: Bool.true :: x6) x4).getD                       x5 Bool.false =                     x1.eval x6 := by
  intro C hC hsize
  refine ⟨encRun 11 C.gates, rwIdx (11+C.gates.length) C.output, ?_, ?_, ?_, ?_⟩
  · rw [len]; exact hsize
  · rw [len]
    have h := idx_bound (11+C.gates.length) C.output
    omega
  · intro i v h
    have hb := earlier C.gates 11 i v h
    omega
  · intro w hw
    change ((encRun 11 C.gates).foldl step (false :: true :: w)).getD
      (rwIdx (11+C.gates.length) C.output) false = _
    have hh : ∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
         g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2 := by
      intro g hg; simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hC g hg
    rw [← hw, preserves _ _ hh, ← tapes]
    exact get_shift _ _
