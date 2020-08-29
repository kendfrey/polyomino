import polyomino.basic
import algebra.group.prod

open polyomino

namespace polyomino.fixed

variables n : ℕ

structure transform :=
(map : equiv.perm (ℤ × ℤ))
(translation : ∀ x y, map (x + y) = map x + y)

namespace transform

  @[ext] lemma ext {x y : transform} : x.map = y.map → x = y :=
  begin
    intros h,
    cases x,
    cases y,
    congr,
    apply h,
  end

  instance : group transform :=
  begin
    refine
    {
      mul := λ x y, ⟨x.map * y.map, _⟩,
      mul_assoc := _,
      one := ⟨1, _⟩,
      one_mul := _,
      mul_one := _,
      inv := λ x, ⟨x.map⁻¹, _⟩,
      mul_left_inv := _,
    },
    {
      simp [x.translation, y.translation],
    },
    {
      simp [mul_assoc],
    },
    {
      simp,
    },
    {
      intros x,
      ext1,
      apply one_mul,
    },
    {
      intros x,
      ext1,
      apply mul_one,
    },
    {
      intros a b,
      apply x.map.injective,
      simp [x.translation],
    },
    {
      intros x,
      ext1,
      apply mul_left_inv,
    },
  end

  @[simp] lemma map_mul (x y : transform) : (x * y).map = x.map * y.map := rfl
  @[simp] lemma map_one : (1 : transform).map = 1 := rfl
  @[simp] lemma map_inv (x : transform) : x⁻¹.map = x.map⁻¹ := rfl

  def of_vector (x : ℤ × ℤ) : transform :=
  begin
    refine ⟨⟨λ y, y + x, λ y, y - x, by intro; simp, by intro; simp⟩, _⟩,
    intros y z,
    dsimp,
    rw [add_assoc y z x, add_assoc y x z, add_comm z x],
  end

  @[simp] lemma of_vector_coe_fn (x y) : ⇑((of_vector (x, y)).map) = λ a, a + (x, y) := rfl

end transform

def equiv (x y : polyomino n) := ∃ t : transform, x.shape.map t.map.to_embedding = y.shape

def setoid {n} : setoid (polyomino n) :=
begin
  use equiv n,
  apply mk_equivalence,
  {
    intros x,
    use 1,
    ext a,
    rw finset.mem_map,
    split,
    {
      rintros ⟨b, b_in_x, b_eq_a⟩,
      rw ← b_eq_a,
      simpa,
    },
    {
      intros a_mem_shape,
      use a,
      split; simp *,
    },
  },
  {
    rintros x y ⟨t, x_equiv_y⟩,
    use t⁻¹,
    ext a,
    rw finset.mem_map,
    rw ← x_equiv_y,
    split,
    {
      rintros ⟨b, b_in_y, b_equiv_a⟩,
      subst a,
      rw finset.mem_map at b_in_y,
      rcases b_in_y with ⟨a, a_in_x, a_equiv_b⟩,
      subst b,
      simpa,
    },
    {
      intros a_in_x,
      use t.map a,
      split,
      {
        rw finset.mem_map,
        use a,
        simpa,
      },
      {
        simp,
      },
    },
  },
  {
    rintros x y z ⟨t, x_equiv_y⟩ ⟨u, y_equiv_z⟩,
    use u * t,
    dsimp,
    ext a,
    rw finset.mem_map,
    split,
    {
      rintros ⟨b, b_in_x, b_equiv_a⟩,
      rw [← y_equiv_z, finset.mem_map],
      use t.map b,
      dsimp at *,
      rw equiv.perm.mul_apply at b_equiv_a,
      refine ⟨_, b_equiv_a⟩,
      rw ← x_equiv_y,
      rw finset.mem_map,
      use b,
      simpa,
    },
    {
      rw [← y_equiv_z, finset.mem_map],
      rintros ⟨b, b_in_y, b_equiv_a⟩,
      use t.map⁻¹ b,
      dsimp at *,
      rw [equiv.perm.mul_apply, equiv.perm.apply_inv_self],
      refine ⟨_, b_equiv_a⟩,
      rw [← x_equiv_y, finset.mem_map] at b_in_y,
      rcases b_in_y with ⟨c, c_in_x, c_equiv_b⟩,
      rw ← c_equiv_b,
      simpa,
    },
  },
end

local attribute [instance] setoid

@[simp] lemma equiv_def (x y : polyomino n) : x ≈ y = ∃ t : transform, x.shape.map t.map.to_embedding = y.shape := rfl

def fixed_polyomino (n) := quotient (@setoid n)

example : fintype (fixed_polyomino 2) :=
begin
  refine ⟨⟨{⟦⟨{⟨0, 0⟩, ⟨0, 1⟩}, by simp, _⟩⟧, ⟦⟨{⟨0, 0⟩, ⟨1, 0⟩}, by simp, _⟩⟧}, _⟩, _⟩,
  {
    apply connected.insert,
    {
      apply finset.mem_singleton_self,
    },
    {
      apply adjacent.up,
    },
    {
      apply connected.singleton,
    },
  },
  {
    apply connected.insert,
    {
      apply finset.mem_singleton_self,
    },
    {
      apply adjacent.right,
    },
    {
      apply connected.singleton,
    },
  },
  {
    apply multiset.coe_nodup.mpr,
    apply list.nodup_cons_of_nodup,
    {
      rw list.mem_singleton,
      rw quotient.eq,
      dsimp,
      rintros ⟨t, contra⟩,
      rw [finset.map_insert, finset.map_singleton, finset.ext_iff] at contra,
      dsimp at contra,
      have contra₁ := (contra ⟨0, 0⟩).mpr (by simp),
      have contra₂ := (contra ⟨1, 0⟩).mpr (by simp),
      clear contra,
      rw [finset.mem_insert, finset.mem_singleton] at *,
      cases contra₁;
      cases contra₂,
      {
        revert contra₂,
        rw ← contra₁,
        exact dec_trivial,
      },
      {
        apply_fun (λ x, x + (0, 1)) at contra₁,
        rw ← t.translation at contra₁,
        simp only [prod.mk_add_mk, zero_add] at contra₁,
        revert contra₂,
        rw ← contra₁,
        exact dec_trivial,
      },
      {
        apply_fun (λ x, x + (0, 1)) at contra₂,
        rw ← t.translation at contra₂,
        simp only [prod.mk_add_mk, zero_add] at contra₂,
        revert contra₂,
        rw ← contra₁,
        exact dec_trivial,
      },
      {
        revert contra₂,
        rw ← contra₁,
        exact dec_trivial,
      },
    },
    {
      apply list.nodup_singleton,
    },
  },
  {
    intros x,
    rw finset.mem_def,
    dsimp,
    rw [multiset.mem_cons, multiset.mem_singleton],
    rw ← quotient.out_eq x,
    cases quotient.out x with s card_s conn_s,
    clear x,
    simp [quotient.eq],
    revert card_s,
    apply connected.induction_on conn_s; clear conn_s s,
    {
      contradiction,
    },
    {
      tidy,
    },
    intros a b s a_not_mem_s b_mem_s adj_a_b ih card_s,
    rw [finset.card_insert_of_not_mem a_not_mem_s, nat.succ_inj', finset.card_eq_one] at card_s,
    cases card_s with c s_eq,
    subst s,
    rw finset.mem_singleton at *,
    subst c,
    cases adj_a_b with x y x y x y x y,
    {
      left,
      use transform.of_vector (-x, -y),
      simp [add_comm],
    },
    {
      left,
      use transform.of_vector (-x, 1 - y),
      simp only [finset.map_insert, finset.map_singleton, equiv.to_embedding_coe_fn, transform.of_vector_coe_fn],
      simp only [prod.mk_add_mk, add_sub_cancel'_right, add_right_neg, add_sub, add_sub_cancel', sub_add_cancel, sub_self],
      exact finset.insert.comm (0, 1) (0, 0) ∅,
    },
    {
      right,
      use transform.of_vector (-x, -y),
      simp [add_comm],
    },
    {
      right,
      use transform.of_vector (1 - x, -y),
      simp only [finset.map_insert, finset.map_singleton, equiv.to_embedding_coe_fn, transform.of_vector_coe_fn],
      simp only [prod.mk_add_mk, add_sub_cancel'_right, add_right_neg, add_sub, add_sub_cancel', sub_add_cancel, sub_self],
      exact finset.insert.comm (1, 0) (0, 0) ∅,
    },
  },
end

end polyomino.fixed