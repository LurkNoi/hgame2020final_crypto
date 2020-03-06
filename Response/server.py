#!/usr/bin/env python3
# -*- coding: utf-8 -*-
import os
import signal
import binascii
import socketserver
import logging
import argparse

from Crypto.Cipher import AES
from Crypto.Util.Padding import pad, unpad

from Alice import KEY, MESSAGE


parser = argparse.ArgumentParser()
parser.add_argument('--debug', action='store_true')
args = parser.parse_args()

DEBUG = args.debug


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
        ip, _ = self.client_address
        logging.basicConfig(
            format=f"[%(asctime)s] [%(process)d] [{ip}]: %(message)s",
            level=logging.DEBUG, 
            datefmt="%H:%M:%S"
        )
        logging.debug("link started".center(40, '-'))

        if DEBUG:
            logging.debug(f"key = {self.KEY.hex()}")

        signal.signal(signal.SIGALRM, self.timeout_handler)
        signal.alarm(60)

        try:
            iv = os.urandom(AES.block_size)

            for _ in range(3):
                name = self.recv(prompt=b'\nWho are you? ')
                if DEBUG:
                    logging.debug(f"iv = {iv.hex()}")
                    logging.debug(f"name = {name}")

                if name == b'Alice':
                    logging.debug('[+] authenticate the server')
                    hex_challenge = self.recv(
                        prompt=b'Give me your challenge (in hex): '
                    )
                    if DEBUG:
                        logging.debug(f"challenge = {hex_challenge}")
                    challenge = binascii.unhexlify(hex_challenge)

                    response = self.encrypt(
                        iv 
                        + self.server_prefix
                        + challenge
                    )
                    hex_response = binascii.hexlify(response)
                    self.send(b'The Response (in hex): ' + hex_response)
                    if DEBUG:
                        logging.debug(f"response = {hex_response}")


                    logging.debug('[+] authenticate Alice')
                    challenge = os.urandom(AES.block_size)
                    hex_challenge = binascii.hexlify(challenge)
                    self.send(b'The Challenge (in hex): ' + hex_challenge)
                    if DEBUG:
                        logging.debug(f"challenge = {hex_challenge}")

                    hex_response = self.recv(
                        prompt=b'Give me your response (in hex): '
                    )
                    if DEBUG:
                        logging.debug(f"response = {hex_response}")
                    response = binascii.unhexlify(hex_response)

                    data = self.decrypt(response)
                    if DEBUG:
                        logging.debug(f"data = {data.hex()}")

                    if (data.startswith(self.alice_prefix)
                            and challenge in data):
                        self.send(b'\nWelcome, Alice.')
                        self.send(b'Here is a message for you: ')
                        self.send(b'\t' + MESSAGE)
                        logging.debug('get the flag'.center(40, '*'))
                    else:
                        self.send(b'Go away hacker!')
                        if not data.startswith(self.alice_prefix):
                            logging.debug('[-] prefix error')
                        if challenge not in data:
                            logging.debug('[-] challenge failed')
                else:
                    self.send(b"You shouldn't be here.")
                    logging.debug('[-] wrong name')
                    break

        except TimeoutError:
            logging.debug('timeout'.center(40, '-'))
            self.request.close()
            exit(1)
        
        except Exception as e:
            if DEBUG:
                logging.debug(str(e))
            logging.debug('error'.center(40, '-'))
            self.request.close()
            exit(2)

        logging.debug('closed'.center(40, '-'))
        self.request.close()


class ForkedServer(socketserver.ForkingMixIn, socketserver.TCPServer):
    pass


if __name__ == "__main__":
    HOST, PORT = '0.0.0.0', 1234
    server = ForkedServer((HOST, PORT), Task)
    server.allow_reuse_address = True
    server.serve_forever()

