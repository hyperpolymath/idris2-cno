# Security Policy

## Supported Versions

| Version | Supported          |
| ------- | ------------------ |
| 0.1.x   | :white_check_mark: |

## Reporting a Vulnerability

If you discover a security vulnerability in idris2-cno, please report it by:

1. **DO NOT** open a public GitHub issue
2. Email the maintainer at security@hyperpolymath.org
3. Include:
   - Description of the vulnerability
   - Steps to reproduce
   - Potential impact
   - Suggested fix (if any)

We will acknowledge receipt within 48 hours and provide a detailed response within 7 days.

## Security Considerations

### CNO Proofs

This library provides compile-time verified identity functions:

- **Proof Verification**: All CNO proofs are verified by the Idris2 type checker
- **No Runtime Bypass**: Identity properties cannot be violated at runtime
- **Composition Safety**: Composed CNOs maintain identity proofs

### Type-Level Security

- CNO records cannot be constructed without valid proofs
- The type system ensures all operations preserve identity
- No unsafe coercions or `believe_me` in core modules

## Security Updates

Security updates will be released as patch versions and announced via:

- GitHub Security Advisories
- Release notes

## Acknowledgments

We thank all security researchers who responsibly disclose vulnerabilities.
