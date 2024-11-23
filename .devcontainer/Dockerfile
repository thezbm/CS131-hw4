FROM --platform=linux/amd64 ubuntu:20.04

## BEGIN: RUNS AS ROOT

# Create a user

ARG USERNAME=cs131
ARG USER_UID=1000
ARG USER_GID=$USER_UID

ENV TZ='Asia/Shanghai'
# !!![zjy] apt change ustc source
RUN apt-get update -y\
    && apt-get install -y --no-install-recommends \
    apt-transport-https \
    ca-certificates \
    tzdata \
    && sed -i "s@http://.*.ubuntu.com@https://mirrors.ustc.edu.cn@g" /etc/apt/sources.list \
    && rm -rf /var/apt/cache/*\
    && apt-get update -y 

RUN groupadd --gid $USER_GID $USERNAME \
    # [Optional] Add sudo support. Omit if you don't need to install software after connecting.
    && apt-get install -y sudo \
    && echo $USERNAME ALL=\(root\) NOPASSWD:ALL > /etc/sudoers.d/$USERNAME \
    && chmod 0440 /etc/sudoers.d/$USERNAME

## Hack needs root permissions
# See hack.sh
COPY hack.sh /tmp/hack.sh
# windows compatibility
RUN dos2unix /tmp/hack.sh
RUN chmod +x /tmp/hack.sh
RUN /tmp/hack.sh

RUN apt-get install -y build-essential
RUN apt-get install -y m4
RUN apt-get install -y opam
RUN apt-get install -y clang
RUN apt-get install -y time
RUN apt-get install -y zip
RUN apt-get install -y zsh

# !!![zjy] install zsh first then set user
RUN useradd --uid $USER_UID --gid $USER_GID -m $USERNAME --shell /bin/zsh 



## Set up user environmnent
COPY .zshrc /home/$USERNAME/
RUN dos2unix /home/$USERNAME/.zshrc
RUN chown $USERNAME /home/$USERNAME/.zshrc

## Run in usermode

# [Optional] Set the default user. Omit if you want to keep the default as root.
USER $USERNAME

RUN mkdir -p /home/$USERNAME/.local/state/
RUN touch /home/$USERNAME/.local/state/utop-history

# Configure opam/ocaml
# !!![zjy] change default repo to github (SJTU repo is failed)
RUN opam init --yes --disable-sandboxing default https://github.com/ocaml/opam-repository.git
RUN opam switch create 4.13.1 ocaml-base-compiler.4.13.1
RUN opam switch 4.13.1
RUN opam install -y dune
RUN opam install -y num
RUN opam install -y menhir
RUN opam install -y utop
RUN opam install -y ocamlformat
RUN opam install -y ocaml-lsp-server
RUN eval `opam config env`

