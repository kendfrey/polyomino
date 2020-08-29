import tactic
import tactic.nth_rewrite

namespace polyomino

inductive adjacent : ℤ × ℤ → ℤ × ℤ → Prop
| up {x y} : adjacent ⟨x, y⟩ ⟨x, y + 1⟩
| down {x y} : adjacent ⟨x, y⟩ ⟨x, y - 1⟩
| right {x y} : adjacent ⟨x, y⟩ ⟨x + 1, y⟩
| left {x y} : adjacent ⟨x, y⟩ ⟨x - 1, y⟩

@[symm] theorem adjacent.symm {x y} : adjacent x y → adjacent y x :=
begin
  intros adj_x_y,
  cases adj_x_y with x y x y x y x y,
  {
    nth_rewrite 1 ← add_sub_cancel y 1,
    apply adjacent.down,
  },
  {
    nth_rewrite 1 ← sub_add_cancel y 1,
    apply adjacent.up,
  },
  {
    nth_rewrite 1 ← add_sub_cancel x 1,
    apply adjacent.left,
  },
  {
    nth_rewrite 1 ← sub_add_cancel x 1,
    apply adjacent.right,
  },
end

inductive connected : finset (ℤ × ℤ) → Prop
| empty : connected ∅
| singleton (x : ℤ × ℤ) : connected {x}
| insert (s x y) : y ∈ s → adjacent x y → connected s → connected (insert x s)

lemma connected.induction_on {p : finset (ℤ × ℤ) → Prop} {s} : connected s → p ∅ → (∀ x, p {x}) → (∀ x y s, x ∉ s → y ∈ s → adjacent x y → connected s → p (insert x s)) → p s :=
begin
  intros conn_s p_empty p_singleton p_insert,
  induction conn_s with _ s₁ a b b_mem_s _ _ ih,
  {
    apply p_empty,
  },
  {
    apply p_singleton,
  },
  clear s,
  rename s₁ s,
  by_cases h : a ∈ s,
  {
    rw finset.insert_eq_of_mem h,
    apply ih,
  },
  {
    apply p_insert; assumption,
  },
end

end polyomino

structure polyomino (n : ℕ) :=
(shape : finset (ℤ × ℤ))
(card : shape.card = n)
(conn : polyomino.connected shape)