#!/usr/bin/env python3
# -*- coding: utf-8 -*-
import os
import signal
import binascii
import socketserver

from Crypto.Cipher import AES
from Crypto.Util.Padding import pad, unpad

from Alice import KEY, MESSAGE


class Task(socketserver.BaseRequestHandler):

    def __init__(self, *args, **kargs):
        self.alice_prefix = b'Alice'
        self.server_prefix = b'Server'
        self.KEY = KEY
        super().__init__(*args, **kargs)

    def _recvall(self):
        BUFF_SIZE = 1024
        data = b''
        while True:
            part = self.request.recv(BUFF_SIZE)
            data += part
            if len(part) < BUFF_SIZE:
                break
        return data.strip()

    def send(self, msg, newline=True):
        try:
            if newline: 
                msg += b'\n'
            self.request.sendall(msg)
        except:
            pass

    def recv(self, prompt=b'> '):
        self.send(prompt, newline=False)
        return self._recvall()

    def encrypt(self, data):
        iv, pt = data[:AES.block_size], data[AES.block_size:]
        pt = pad(pt, AES.block_size)
        aes = AES.new(self.KEY, AES.MODE_CBC, iv=iv)
        ct = aes.encrypt(pt)
        return iv + ct

    def decrypt(self, data, unpad_pt=False):
        iv, ct = data[:AES.block_size], data[AES.block_size:]
        aes = AES.new(self.KEY, AES.MODE_CBC, iv=iv)
        pt = aes.decrypt(ct)
        if unpad_pt:
            pt = unpad(pt, AES.block_size)
        return pt

    def timeout_handler(self, signum, frame):
        self.send(b"\n\nSorry, time out.\n")
        raise TimeoutError

    def handle(self):
        signal.signal(signal.SIGALRM, self.timeout_handler)
        signal.alarm(60)

        try:
            iv = os.urandom(AES.block_size)

            for _ in range(3):
                name = self.recv(prompt=b'\nWho are you? ')
                if name == b'Alice':
                    # authenticate the server
                    hex_challenge = self.recv(
                        prompt=b'Give me your challenge (in hex): '
                    )
                    challenge = binascii.unhexlify(hex_challenge)
                    response = self.encrypt(
                        iv 
                        + self.server_prefix
                        + challenge
                    )
                    hex_response = binascii.hexlify(response)
                    self.send(b'The Response (in hex): ' + hex_response)

                    # authenticate Alice
                    challenge = os.urandom(AES.block_size)
                    hex_challenge = binascii.hexlify(challenge)
                    self.send(b'The Challenge (in hex): ' + hex_challenge)
                    hex_response = self.recv(
                        prompt=b'Give me your response (in hex): '
                    )
                    response = binascii.unhexlify(hex_response)
                    data = self.decrypt(response)
                    if (data.startswith(self.alice_prefix)
                            and challenge in data):
                        self.send(b'\nWelcome, Alice.')
                        self.send(b'Here is a message for you: ')
                        self.send(b'\t' + MESSAGE)
                    else:
                        self.send(b'Go away hacker!')
                else:
                    self.send(b"You shouldn't be here.")
                    break

        except:
            pass

        self.request.close()


class ForkedServer(socketserver.ForkingMixIn, socketserver.TCPServer):
    pass


if __name__ == "__main__":
    HOST, PORT = '0.0.0.0', 1234
    server = ForkedServer((HOST, PORT), Task)
    server.allow_reuse_address = True
    server.serve_forever()

