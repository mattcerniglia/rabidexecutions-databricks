FROM rust:1.88-slim-bookworm AS build
WORKDIR /src
COPY Cargo.toml ./
COPY .cargo .cargo
COPY src src
RUN cargo build --release && cp target/release/shopping /shopping

FROM debian:bookworm-slim
COPY --from=build /shopping /app/shopping
ENV GLIBC_TUNABLES=glibc.malloc.hugetlb=1
WORKDIR /app
CMD ["/app/shopping"]
