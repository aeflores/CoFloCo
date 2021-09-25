FROM ubuntu:20.04 

RUN ln -fs /usr/share/zoneinfo/America/New_York /etc/localtime

RUN apt-get -y update && apt-get -y install swi-prolog wget libgmp-dev unzip

RUN wget https://www.bugseng.com/products/ppl/download/ftp/releases/1.2/ppl-1.2.zip \
    && unzip ppl-1.2.zip \
    && cd ppl-1.2 \
    && ./configure --enable-interfaces=swi_prolog,yap_prolog \
    && make && make install

ENV LD_LIBRARY_PATH=$LD_LIBRARY_PATH:/usr/local/lib/ppl/:/usr/local/lib/
COPY . /cofloco
ENV PATH=$PATH:/cofloco
WORKDIR /cofloco