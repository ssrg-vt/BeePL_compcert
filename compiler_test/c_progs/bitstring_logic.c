#include <stdio.h>

struct bytes_t {
    unsigned char *start;
    unsigned char *end;
};

struct xdp_md_wrapper {
    struct bytes_t data;
    unsigned long data_meta;
};

struct xdp_md {
    unsigned long data;
    unsigned long data_end;
    unsigned long data_meta;
};

struct ethhdr {
    unsigned int dst;
    unsigned int src;
};

int parse (struct xdp_md *ctx) {
    struct xdp_md_wrapper xdp_md_wrapper;
    xdp_md_wrapper.data.start = (unsigned char *)ctx->data;
    xdp_md_wrapper.data.end = (unsigned char *)ctx->data_end;
    struct ethhdr eth;
    // Ensures the size of the data buffer is greater than or equal to the size of the ethhdr structure
    // Which means we have enough data to parse it into the ethhdr structure
    if (xdp_md_wrapper.data.start + sizeof(struct ethhdr) > xdp_md_wrapper.data.end) {
        return -1; }

    // Does the copy of the data from the xdp_md_wrapper to the eth structure
    struct ethhdr *temp = (struct ethhdr *) xdp_md_wrapper.data.start;
    eth.dst = temp->dst;
    eth.src = temp->src;
    xdp_md_wrapper.data.start = xdp_md_wrapper.data.start + sizeof(struct ethhdr);
    return 0;
}

int main() {
    struct xdp_md ctx = {0};

    unsigned char data[100];
    unsigned long meta = 10;

    ctx.data = (unsigned long)data;
    ctx.data_end = (unsigned long)(data + sizeof(data));
    ctx.data_meta = meta;

    parse(&ctx);

    if (parse(&ctx) == -1) {
        printf("Parse failed\n");
        return -1;
    }
    printf("Parse succeeded\n");
    return 0;
}


