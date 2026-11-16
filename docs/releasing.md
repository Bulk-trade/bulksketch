# Publishing and API documentation

Releases use GitHub Actions and crates.io Trusted Publishing (OIDC).
There is no saved Cargo API token in the release workflow. The publish job
exchanges its GitHub identity for a short-lived crates.io token, uses it only
for `cargo publish`, and revokes it when the job finishes.

## First publication

As of November 2026, crates.io requires an API token to create a new crate.
Trusted Publishing can publish versions of an existing crate, but cannot
create one. See the [crates.io Trusted Publishing documentation](https://crates.io/docs/trusted-publishing).

The first upload uses the separately authorized, manual
[first-publication workflow](../.github/workflows/bootstrap.yml). It accepts
only version `0.1.0` from an explicitly selected commit on `main`, runs the
native tests and publication dry run, and stops if the crate already exists.
Its one-time token is the `CRATES_IO_BOOTSTRAP_TOKEN` secret in the
`crates-io-bootstrap` environment, restricted to `main`. Enter the token
directly in GitHub; never put it in a local Cargo login, a file or a message.
Delete the secret, revoke the token and remove the bootstrap workflow after
the first successful publication.

Create the token with only the `publish-new` scope, the exact crate name
pattern `bulksketch`, and a custom expiration date of tomorrow. The publishing
account must have a verified email address. Deleting a GitHub secret does not
revoke its crates.io token; revoke it separately in crates.io token settings.

Do not push the first release tag before the bootstrap is complete. While
creating that first tag, leave the ordinary Release workflow disabled to avoid
uploading the same version twice. Enable it after configuring the trusted
publisher below. Subsequent release tags use OIDC, with no saved-token fallback.

## Trusted publisher configuration

After the crate exists, a crates.io owner must add this GitHub publisher in the
crate's settings:

| Field | Value |
| --- | --- |
| Repository owner | `Bulk-trade` |
| Repository name | `bulksketch` |
| Workflow filename | `release.yml` |
| Environment | `crates-io` |

The GitHub `crates-io` environment permits release tags matching `v*`.
The workflow also checks that the tagged commit belongs to `main`, that its
package is `bulksketch`, and that the tag matches the version in `Cargo.toml`.
Only the publish job can request a crates.io OIDC token. Pull requests and
ordinary branch pushes cannot publish a crate.

## Subsequent releases

1. Update `Cargo.toml`, the changelog and dependent proof fingerprints. Run the
   checks in [CONTRIBUTING.md](../CONTRIBUTING.md), including the full proof
   pipeline when a pinned build input changes.
2. Push the validated commit to `main`. Confirm that CI passes.
3. Create an annotated tag `v<package version>` at that commit and push the tag.
4. The [Release workflow](../.github/workflows/release.yml) checks the tag,
   runs release tests, builds Rustdoc with warnings denied and performs a
   publication dry run. Its separate publish job then authenticates through
   OIDC and uploads the crate.
5. Confirm the version and package checksum on crates.io, and confirm that its
   docs.rs build succeeds. Registry publication is permanent; inspect the
   package contents before tagging.

## Rustdoc

The API documentation for `main` is hosted at
[bulk-trade.github.io/bulksketch](https://bulk-trade.github.io/bulksketch/).
The [Rustdoc workflow](../.github/workflows/docs.yml) builds the public API with
`RUSTDOCFLAGS="-D warnings" cargo doc --no-deps --locked` and deploys it to
GitHub Pages after each push to `main`. GitHub Pages uses the Actions build
source and the `github-pages` environment, restricted to `main`.

[docs.rs automatically builds documentation](https://docs.rs/about/builds) for
each version uploaded to crates.io. Once a release is published, its stable
API documentation will be at `https://docs.rs/bulksketch/<version>/bulksketch/`.
The Pages site tracks `main`; docs.rs tracks published versions.
