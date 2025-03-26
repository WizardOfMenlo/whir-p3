use p3_field::{Field, TwoAdicField};

/// Defines a domain over which finite field (I)FFTs can be performed. Works
/// only for fields that have a large multiplicative subgroup of size that is
/// a power-of-2.
#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub struct Radix2EvaluationDomain<F> {
    /// The size of the domain.
    pub size: u64,
    /// `log_2(self.size)`.
    pub log_size_of_group: u32,
    /// Size of the domain as a field element.
    pub size_as_field_element: F,
    /// Inverse of the size in the field.
    pub size_inv: F,
    /// A generator of the subgroup.
    pub group_gen: F,
    /// Inverse of the generator of the subgroup.
    pub group_gen_inv: F,
    /// Offset that specifies the coset.
    pub offset: F,
    /// Inverse of the offset that specifies the coset.
    pub offset_inv: F,
    /// Constant coefficient for the vanishing polynomial.
    /// Equals `self.offset^self.size`.
    pub offset_pow_size: F,
}

impl<F: Field + TwoAdicField> Radix2EvaluationDomain<F> {
    pub fn new(num_coeffs: usize) -> Option<Self> {
        let size = num_coeffs.next_power_of_two() as u64;
        let log_size_of_group = size.trailing_zeros();

        if log_size_of_group > F::TWO_ADICITY as u32 {
            return None;
        }

        // Compute the generator for the multiplicative subgroup.
        // It should be the 2^(log_size_of_group) root of unity.
        let group_gen = F::two_adic_generator(log_size_of_group as usize);

        // Check that it is indeed the 2^(log_size_of_group) root of unity.
        debug_assert_eq!(group_gen.exp_u64(size), F::ONE);
        let size_as_field_element = F::from_u64(size);
        let size_inv = size_as_field_element.inverse();

        Some(Self {
            size,
            log_size_of_group,
            size_as_field_element,
            size_inv,
            group_gen,
            group_gen_inv: group_gen.inverse(),
            offset: F::ONE,
            offset_inv: F::ONE,
            offset_pow_size: F::ONE,
        })
    }

    #[inline]
    pub const fn size(&self) -> usize {
        self.size as usize
    }

    #[inline]
    pub const fn group_gen(&self) -> F {
        self.group_gen
    }

    #[inline]
    pub const fn group_gen_inv(&self) -> F {
        self.group_gen_inv
    }

    #[inline]
    pub const fn log_size_of_group(&self) -> u32 {
        self.log_size_of_group
    }

    #[inline]
    pub const fn size_inv(&self) -> F {
        self.size_inv
    }

    #[inline]
    pub const fn coset_offset(&self) -> F {
        self.offset
    }

    #[inline]
    pub const fn coset_offset_inv(&self) -> F {
        self.offset_inv
    }

    #[inline]
    pub const fn coset_offset_pow_size(&self) -> F {
        self.offset_pow_size
    }
}

#[cfg(test)]
mod tests {
    use p3_baby_bear::BabyBear;
    use p3_field::PrimeCharacteristicRing;

    use super::*;

    #[test]
    fn test_domain_creation() {
        let domain = Radix2EvaluationDomain::<BabyBear>::new(8).unwrap();
        assert_eq!(domain.size(), 8);
        assert_eq!(domain.log_size_of_group, 3);
    }

    #[test]
    fn test_invalid_domain() {
        // BabyBear has TWO_ADICITY = 27, so we ensure that we test an invalid size
        // that exceeds the maximum power-of-2 allowed.
        let invalid_size = 1 << (BabyBear::TWO_ADICITY + 1); // 2^(27+1)
        assert!(Radix2EvaluationDomain::<BabyBear>::new(invalid_size).is_none());
    }

    #[test]
    fn test_root_of_unity() {
        let domain = Radix2EvaluationDomain::<BabyBear>::new(8).unwrap();
        let root = domain.group_gen();

        let expected = root.exp_u64(8);
        assert_eq!(expected, BabyBear::ONE);
    }

    #[test]
    fn test_size_conversion() {
        let domain = Radix2EvaluationDomain::<BabyBear>::new(16).unwrap();
        assert_eq!(domain.size(), 16);
    }

    #[test]
    fn test_group_gen_inverse() {
        let domain = Radix2EvaluationDomain::<BabyBear>::new(16).unwrap();
        assert_eq!(domain.group_gen() * domain.group_gen_inv(), BabyBear::ONE);
    }

    #[test]
    fn test_size_inv() {
        let domain = Radix2EvaluationDomain::<BabyBear>::new(16).unwrap();
        assert_eq!(
            domain.size_as_field_element * domain.size_inv(),
            BabyBear::ONE
        );
    }

    #[test]
    fn test_coset_offset() {
        let domain = Radix2EvaluationDomain::<BabyBear>::new(16).unwrap();
        assert_eq!(domain.coset_offset(), BabyBear::ONE);
        assert_eq!(domain.coset_offset_inv(), BabyBear::ONE);
        assert_eq!(domain.coset_offset_pow_size(), BabyBear::ONE);
    }
}
