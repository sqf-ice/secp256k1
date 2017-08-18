#ifndef _HASH_H_
#define _HASH_H_

namespace ripemd160 {
void Transform(unsigned char* out, const unsigned char* in);
}

namespace sha256 {
void Transform(unsigned char* out, const unsigned char* in);
}

namespace sha256_8way {
void Transform(unsigned char* out1, unsigned char* out2, unsigned char* out3, unsigned char* out4, unsigned char* out5, unsigned char* out6, unsigned char* out7, unsigned char* out8, const unsigned char* in);
}

namespace ripemd160_8way {
void Transform(unsigned char* out1, unsigned char* out2, unsigned char* out3, unsigned char* out4, unsigned char* out5, unsigned char* out6, unsigned char* out7, unsigned char* out8, const unsigned char* in);
}

#endif
