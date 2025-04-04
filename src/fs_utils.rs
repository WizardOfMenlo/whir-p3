use p3_field::Field;

use crate::fiat_shamir::{codecs::traits::FieldDomainSeparator, pow::traits::PoWDomainSeparator};

/// Trait for adding out-of-domain (OOD) queries and their responses to an DomainSeparator.
///
/// This trait allows extending an DomainSeparator with challenge-response interactions.
pub trait OODDomainSeparator<F: Field> {
    /// Adds `num_samples` OOD queries and their corresponding responses to the DomainSeparator.
    ///
    /// - If `num_samples > 0`, this appends:
    ///   - A challenge query labeled `"ood_query"` with `num_samples` elements.
    ///   - A corresponding response labeled `"ood_ans"` with `num_samples` elements.
    /// - If `num_samples == 0`, the DomainSeparator remains unchanged.
    #[must_use]
    fn add_ood(self, num_samples: usize) -> Self;
}

impl<F, DomainSeparator> OODDomainSeparator<F> for DomainSeparator
where
    F: Field,
    DomainSeparator: FieldDomainSeparator<F>,
{
    fn add_ood(self, num_samples: usize) -> Self {
        if num_samples > 0 {
            self.challenge_scalars(num_samples, "ood_query")
                .add_scalars(num_samples, "ood_ans")
        } else {
            self
        }
    }
}

/// Trait for adding a Proof-of-Work (PoW) challenge to an DomainSeparator.
///
/// This trait enables an DomainSeparator to include PoW challenges.
pub trait WhirPoWDomainSeparator {
    /// Adds a Proof-of-Work challenge to the DomainSeparator.
    ///
    /// - If `bits > 0`, this appends a PoW challenge labeled `"pow_queries"`.
    /// - If `bits == 0`, the DomainSeparator remains unchanged.
    #[must_use]
    fn pow(self, bits: f64) -> Self;
}

impl<DomainSeparator> WhirPoWDomainSeparator for DomainSeparator
where
    DomainSeparator: PoWDomainSeparator,
{
    fn pow(self, bits: f64) -> Self {
        if bits > 0. {
            self.challenge_pow("pow_queries")
        } else {
            self
        }
    }
}

#[cfg(test)]
mod tests {
    use p3_baby_bear::BabyBear;

    use super::*;
    use crate::fiat_shamir::domain_separator::DomainSeparator;

    #[test]
    fn test_add_ood() {
        let iop: DomainSeparator = DomainSeparator::new("test_protocol");

        // Apply OOD query addition
        let updated_iop =
            <DomainSeparator as OODDomainSeparator<BabyBear>>::add_ood(iop.clone(), 3);

        // Convert to a string for inspection
        let pattern_str = String::from_utf8(updated_iop.as_bytes().to_vec()).unwrap();

        // Check if "ood_query" and "ood_ans" were correctly appended
        assert!(pattern_str.contains("ood_query"));
        assert!(pattern_str.contains("ood_ans"));

        // Test case where num_samples = 0 (should not modify anything)
        let unchanged_iop = <DomainSeparator as OODDomainSeparator<BabyBear>>::add_ood(iop, 0);
        let unchanged_str = String::from_utf8(unchanged_iop.as_bytes().to_vec()).unwrap();
        assert_eq!(unchanged_str, "test_protocol"); // Should remain the same
    }

    #[test]
    fn test_pow() {
        let iop: DomainSeparator = DomainSeparator::new("test_protocol");

        // Apply PoW challenge
        let updated_iop = iop.clone().pow(10.0);

        // Convert to a string for inspection
        let pattern_str = String::from_utf8(updated_iop.as_bytes().to_vec()).unwrap();

        // Check if "pow_queries" was correctly added
        assert!(pattern_str.contains("pow_queries"));

        // Test case where bits = 0 (should not modify anything)
        let unchanged_iop = iop.pow(0.0);
        let unchanged_str = String::from_utf8(unchanged_iop.as_bytes().to_vec()).unwrap();
        assert_eq!(unchanged_str, "test_protocol"); // Should remain the same
    }
}
