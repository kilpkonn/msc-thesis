#import "@preview/codelst:2.0.0": sourcecode

= Appendix 1: List of crates <appendix-crates>
#table(
  columns: (auto, auto),
  inset: 5pt,
  align: horizon,
  [*Category*], [*Crate*],
[algorithms], [rand-0.8.5],
[algorithms], [num-traits-0.2.18],
[algorithms], [crossbeam-utils-0.8.19],
[algorithms], [rand_core-0.6.4],
[algorithms], [rand_chacha-0.3.1],
[api-bindings], [flate2-1.0.28],
[api-bindings], [openssl-0.10.64],
[api-bindings], [socket2-0.5.6],
[api-bindings], [libloading-0.8.3],
[api-bindings], [zstd-safe-7.0.0],
[asynchronous], [mio-0.8.11],
[asynchronous], [tokio-1.36.0],
[asynchronous], [futures-0.3.30],
[asynchronous], [tokio-util-0.7.10],
[asynchronous], [tracing-0.1.40],
[command-line-interface], [clap-4.5.2],
[command-line-interface], [textwrap-0.16.1],
[command-line-interface], [clap_lex-0.7.0],
[command-line-interface], [clap_derive-4.5.0],
[command-line-interface], [os_str_bytes-7.0.0],
[command-line-utilities], [crossterm-0.27.0],
[command-line-utilities], [inferno-0.11.19],
[command-line-utilities], [names-0.14.0],
[command-line-utilities], [honggfuzz-0.5.55],
[command-line-utilities], [self_update-0.39.0],
[concurrency], [crossbeam-utils-0.8.19],
[concurrency], [crossbeam-channel-0.5.12],
[concurrency], [parking_lot_core-0.9.9],
[concurrency], [parking_lot-0.12.1],
[concurrency], [lock_api-0.4.11],
[cryptography], [digest-0.10.7],
[cryptography], [sha2-0.10.8],
[cryptography], [rustls-0.23.1],
[cryptography], [block-buffer-0.10.4],
[cryptography], [ppv-lite86-0.2.17],
[cryptography], [rustls-0.23.2],
[data-structures], [hashbrown-0.14.3],
[data-structures], [smallvec-1.13.1],
[data-structures], [indexmap-2.2.5],
[data-structures], [semver-1.0.22],
[data-structures], [bytes-1.5.0],
[database], [rocksdb-0.22.0],
[database], [postgres-types-0.2.6],
[database], [diesel-2.1.4],
[database], [rusqlite-0.31.0],
[database], [librocksdb-sys-6.20.3],
[development-tools], [syn-2.0.52],
[development-tools], [autocfg-1.1.0],
[development-tools], [proc-macro2-1.0.79],
[development-tools], [quote-1.0.35],
[development-tools], [log-0.4.21],
[embedded], [ciborium-io-0.2.2],
[embedded], [ciborium-0.2.2],
[embedded], [bitvec-1.0.1],
[embedded], [oorandom-11.1.3],
[embedded], [ciborium-ll-0.2.2],
[encoding], [serde_json-1.0.114],
[encoding], [byteorder-1.5.0],
[encoding], [url-2.5.0],
[encoding], [serde-1.0.197],
[encoding], [base64-0.22.0],
[external-ffi-bindings], [libc-0.2.153],
[external-ffi-bindings], [linux-raw-sys-0.6.4],
[external-ffi-bindings], [winapi-util-0.1.6],
[external-ffi-bindings], [winapi-0.3.9],
[external-ffi-bindings], [openssl-sys-0.9.101],
[filesystem], [glob-0.3.1],
[filesystem], [which-6.0.0],
[filesystem], [remove_dir_all-0.8.2],
[filesystem], [rustix-0.38.31],
[filesystem], [walkdir-2.5.0],
[game-development], [gpu-alloc-0.6.0],
[game-development], [gpu-alloc-types-0.3.0],
[game-development], [egui-winit-0.26.2],
[game-development], [egui-0.26.2],
[game-development], [eframe-0.26.2],
[graphics], [rgb-0.8.37],
[graphics], [exr-1.72.0],
[graphics], [tiny-skia-path-0.11.4],
[graphics], [gpu-alloc-0.6.0],
[graphics], [gpu-alloc-types-0.3.0],
[gui], [winit-0.29.14],
[gui], [winit-0.29.15],
[gui], [stdweb-0.4.20],
[gui], [stdweb-internal-macros-0.2.9],
[gui], [stdweb-derive-0.5.3],
[gui], [stdweb-internal-runtime-0.1.5],
[hardware-support], [num_cpus-1.16.0],
[hardware-support], [portable-atomic-1.6.0],
[hardware-support], [safe_arch-0.7.1],
[hardware-support], [cpufeatures-0.2.12],
[hardware-support], [num_threads-0.1.7],
[mathematics], [nalgebra-0.32.4],
[mathematics], [smawk-0.3.2],
[mathematics], [crypto-bigint-0.5.5],
[mathematics], [rust_decimal-1.34.3],
[mathematics], [bigdecimal-0.4.3],
[multimedia], [image-0.25.0],
[multimedia], [tiff-0.9.1],
[multimedia], [png-0.17.13],
[multimedia], [rgb-0.8.37],
[multimedia], [exr-1.72.0],
[network-programming], [socket2-0.5.6],
[network-programming], [h2-0.4.2],
[network-programming], [bytes-1.5.0],
[network-programming], [tokio-1.36.0],
[network-programming], [hyper-1.2.0],
[no-std], [libc-0.2.153],
[no-std], [rand_core-0.6.4],
[no-std], [serde-1.0.197],
[no-std], [rand-0.8.5],
[no-std], [bitflags-2.4.2],
[os], [nix-0.28.0],
[os], [rustix-0.38.31],
[os], [libc-0.2.153],
[os], [getrandom-0.2.12],
[os], [winapi-0.3.9],
[parser-implementations], [syn-2.0.52],
[parser-implementations], [serde_json-1.0.114],
[parser-implementations], [time-0.3.34],
[parser-implementations], [url-2.5.0],
[parser-implementations], [toml-0.8.11],
[parsing], [byteorder-1.5.0],
[parsing], [toml-0.8.11],
[parsing], [nom-7.1.3],
[parsing], [semver-parser-0.10.2],
[parsing], [minimal-lexical-0.2.1],
[rendering], [unic-ucd-version-0.9.0],
[rendering], [gl_generator-0.14.0],
[rendering], [unic-ucd-segment-0.9.0],
[rendering], [unic-segment-0.9.0],
[rendering], [khronos_api-3.1.0],
[rust-patterns], [scopeguard-1.2.0],
[rust-patterns], [itertools-0.12.1],
[rust-patterns], [lazy_static-1.4.0],
[rust-patterns], [once_cell-1.19.0],
[rust-patterns], [thiserror-1.0.58],
[science], [num-traits-0.2.18],
[science], [num-integer-0.1.46],
[science], [num-bigint-0.4.4],
[science], [num-rational-0.4.1],
[science], [num-complex-0.4.5],
[text-processing], [strsim-0.11.0],
[text-processing], [regex-1.10.3],
[text-processing], [aho-corasick-1.1.2],
[text-processing], [textwrap-0.16.1],
[text-processing], [unicode-bidi-0.3.15],
[wasm], [uuid-1.7.0],
[wasm], [wasi-0.13.0+wasi-0.2.0],
[wasm], [reqwest-0.11.26],
[wasm], [wasm-bindgen-0.2.92],
[wasm], [js-sys-0.3.69],
[web-programming], [hyper-1.2.0],
[web-programming], [http-1.1.0],
[web-programming], [h2-0.4.2],
[web-programming], [httparse-1.8.0],
[web-programming], [url-2.5.0],
)

= Appendix 2: Highly generic code example <appendix-generics>
#figure(
sourcecode()[
```rs
impl<T, R: Dim, C: Dim, S> AbsDiffEq for Unit<Matrix<T, R, C, S>>
where
    T: Scalar + AbsDiffEq,
    S: RawStorage<T, R, C>,
    T::Epsilon: Clone,
{
    type Epsilon = T::Epsilon;

    #[inline]
    fn default_epsilon() -> Self::Epsilon {
        T::default_epsilon()
    }

    #[inline]
    fn abs_diff_eq(&self, other: &Self, epsilon: Self::Epsilon) -> bool {
        self.as_ref().abs_diff_eq(other.as_ref(), epsilon)
    }
}
```],
caption: [
    `nalgebra` code example
  ],
) <eval-nalgebra>