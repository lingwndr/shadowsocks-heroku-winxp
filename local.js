"use strict"; //declaring strict mode for "Block-scoped declarations (let, const, function, class)"
const net = require('net');
const url = require('url');
const http = require('http');
const fs = require('fs');
const path = require('path');
const WebSocket = require('ws');
const parseArgs = require('minimist');
const HttpsProxyAgent = require('https-proxy-agent');
//const { Encryptor } = require('./encrypt');

///////*from encrypt.js *////////
const crypto = require('crypto');
//const { merge_sort } = require('./merge_sort');
const int32Max = Math.pow(2, 32);
const cachedTables = {}; // password: [encryptTable, decryptTable]
///////*from encrypt.js *////////


///////* from merg_sort.js *//////
const merge = function(left, right, comparison) {
  const result = new Array();
  while (left.length > 0 && right.length > 0) {
    if (comparison(left[0], right[0]) <= 0) {
      result.push(left.shift());
    } else {
      result.push(right.shift());
    }
  }
  while (left.length > 0) {
    result.push(left.shift());
  }
  while (right.length > 0) {
    result.push(right.shift());
  }
  return result;
};
var merge_sort = function(array, comparison) {
  if (array.length < 2) {
    return array;
  }
  const middle = Math.ceil(array.length / 2);
  return merge(
    merge_sort(array.slice(0, middle), comparison),
    merge_sort(array.slice(middle), comparison),
    comparison
  );
};
///////* from merg_sort.js *//////

///////*from encrypt.js *////////
const getTable = function(key) {
  if (cachedTables[key]) {
    return cachedTables[key];
  }
  console.log('calculating ciphers');
  let table = new Array(256);
  const decrypt_table = new Array(256);
  const md5sum = crypto.createHash('md5');
  md5sum.update(key);
  const hash = new Buffer(md5sum.digest(), 'binary');
  const al = hash.readUInt32LE(0);
  const ah = hash.readUInt32LE(4);
  let i = 0;

  while (i < 256) {
    table[i] = i;
    i++;
  }
  i = 1;

  while (i < 1024) {
    table = merge_sort(
      table,
      (x, y) =>
        ((ah % (x + i)) * int32Max + al) % (x + i) -
        ((ah % (y + i)) * int32Max + al) % (y + i)
    );
    i++;
  }
  i = 0;
  while (i < 256) {
    decrypt_table[table[i]] = i;
    ++i;
  }
  const result = [table, decrypt_table];
  cachedTables[key] = result;
  return result;
};
const substitute = function(table, buf) {
  let i = 0;

  while (i < buf.length) {
    buf[i] = table[buf[i]];
    i++;
  }
  return buf;
};

const bytes_to_key_results = {};
const EVP_BytesToKey = function(password, key_len, iv_len) {
  if (bytes_to_key_results[`${password}:${key_len}:${iv_len}`]) {
    return bytes_to_key_results[`${password}:${key_len}:${iv_len}`];
  }
  const m = [];
  let i = 0;
  let count = 0;
  while (count < key_len + iv_len) {
    const md5 = crypto.createHash('md5');
    let data = password;
    if (i > 0) {
      data = Buffer.concat([m[i - 1], password]);
    }
    md5.update(data);
    const d = md5.digest();
    m.push(d);
    count += d.length;
    i += 1;
  }
  const ms = Buffer.concat(m);
  const key = ms.slice(0, key_len);
  const iv = ms.slice(key_len, key_len + iv_len);
  bytes_to_key_results[password] = [key, iv];
  return [key, iv];
};
const method_supported = {
  'aes-128-cfb': [16, 16],
  'aes-192-cfb': [24, 16],
  'aes-256-cfb': [32, 16],
  'bf-cfb': [16, 8],
  'camellia-128-cfb': [16, 16],
  'camellia-192-cfb': [24, 16],
  'camellia-256-cfb': [32, 16],
  'cast5-cfb': [16, 8],
  'des-cfb': [8, 8],
  'idea-cfb': [16, 8],
  'rc2-cfb': [16, 8],
  rc4: [16, 0],
  'rc4-md5': [16, 16],
  'seed-cfb': [16, 16]
};
const create_rc4_md5_cipher = function(key, iv, op) {
  const md5 = crypto.createHash('md5');
  md5.update(key);
  md5.update(iv);
  const rc4_key = md5.digest();
  if (op === 1) {
    return crypto.createCipheriv('rc4', rc4_key, '');
  } else {
    return crypto.createDecipheriv('rc4', rc4_key, '');
  }
};
class Encryptor {
  constructor(key, method) {
    this.key = key;
    this.method = method;
    this.iv_sent = false;
    if (this.method === 'table') {
      this.method = null;
    }
    if (this.method) {
      this.cipher = this.get_cipher(
        this.key,
        this.method,
        1,
        crypto.randomBytes(32)
      );
    } else {
      //[this.encryptTable, this.decryptTable] = getTable(this.key);
      //destructuring syntax not supported in older versions of node
      //replaced with follwing lines
      const temp = getTable(this.key)
      this.encryptTable = temp[0]
      this.decryptTable = temp[1]
    }
  }

  get_cipher_len(method) {
    method = method.toLowerCase();
    return method_supported[method];
  }

  get_cipher(password, method, op, iv) {
    method = method.toLowerCase();
    password = new Buffer(password, 'binary');
    const m = this.get_cipher_len(method);
    if (m) {
      //const [key, iv_] = EVP_BytesToKey(password, m[0], m[1]);
      //destructuring syntax not supported in older versions of node
      //replaced with follwing lines
      const tmp = EVP_BytesToKey(password, m[0], m[1]);
      const key = tmp[0]
      const iv_ = tmp[1]
      if (!iv) {
        iv = iv_;
      }
      if (op === 1) {
        this.cipher_iv = iv.slice(0, m[1]);
      }
      iv = iv.slice(0, m[1]);
      if (method === 'rc4-md5') {
        return create_rc4_md5_cipher(key, iv, op);
      } else {
        if (op === 1) {
          return crypto.createCipheriv(method, key, iv);
        } else {
          return crypto.createDecipheriv(method, key, iv);
        }
      }
    }
  }

  encrypt(buf) {
    if (this.method) {
      const result = this.cipher.update(buf);
      if (this.iv_sent) {
        return result;
      } else {
        this.iv_sent = true;
        return Buffer.concat([this.cipher_iv, result]);
      }
    } else {
      return substitute(this.encryptTable, buf);
    }
  }

  decrypt(buf) {
    if (this.method) {
      let result;
      if (!this.decipher) {
        const decipher_iv_len = this.get_cipher_len(this.method)[1];
        const decipher_iv = buf.slice(0, decipher_iv_len);
        this.decipher = this.get_cipher(this.key, this.method, 0, decipher_iv);
        result = this.decipher.update(buf.slice(decipher_iv_len));
        return result;
      } else {
        result = this.decipher.update(buf);
        return result;
      }
    } else {
      return substitute(this.decryptTable, buf);
    }
  }
}
///////*from encrypt.js *////////

const options = {
  alias: {
    b: 'local_address',
    l: 'local_port',
    s: 'server',
    r: 'remote_port',
    k: 'password',
    c: 'config_file',
    m: 'method'
  },
  string: [
    'local_address',
    'server',
    'password',
    'config_file',
    'method',
    'scheme'
  ],
  default: {
    config_file: path.resolve(__dirname, 'config.json')
  }
};

const inetNtoa = buf => buf[0] + '.' + buf[1] + '.' + buf[2] + '.' + buf[3];

const configFromArgs = parseArgs(process.argv.slice(2), options);
const configContent = fs.readFileSync(configFromArgs.config_file);
const config = JSON.parse(configContent);
for (let k in configFromArgs) {
  const v = configFromArgs[k];
  config[k] = v;
}

const SCHEME = config.scheme;
let SERVER = config.server;
const REMOTE_PORT = config.remote_port;
const LOCAL_ADDRESS = config.local_address;
const PORT = config.local_port;
const KEY = config.password;
let METHOD = config.method;
const timeout = Math.floor(config.timeout * 1000);

/*
if (['', 'null', 'table'].includes(METHOD.toLowerCase())) {
  METHOD = null;
}
*/ //replaced with ...
if (METHOD.toLowerCase() == '' || METHOD.toLowerCase() == 'null' || METHOD.toLowerCase() == 'table'){
    METHOD = null;
}

const HTTPPROXY = process.env.http_proxy;

if (HTTPPROXY) {
  console.log('http proxy:', HTTPPROXY);
}

const prepareServer = function(address) {
  const serverUrl = url.parse(address);
  serverUrl.slashes = true;
  if (!serverUrl.protocol) {
    serverUrl.protocol = SCHEME;
  }
  if (!serverUrl.hostname) {
    serverUrl.hostname = address;
    serverUrl.pathname = '/';
  }
  if (!serverUrl.port) {
    serverUrl.port = REMOTE_PORT;
  }
  return url.format(serverUrl);
};

if (SERVER instanceof Array) {
  SERVER = SERVER.map(s => prepareServer(s));
} else {
  SERVER = prepareServer(SERVER);
}

const getServer = function() {
  if (SERVER instanceof Array) {
    return SERVER[Math.floor(Math.random() * SERVER.length)];
  } else {
    return SERVER;
  }
};

var server = net.createServer(function(connection) {
  console.log('local connected');
  server.getConnections(function(err, count) {
    console.log('concurrent connections:', count);
  });
  const encryptor = new Encryptor(KEY, METHOD);
  let stage = 0;
  let headerLength = 0;
  let cachedPieces = [];
  let addrLen = 0;
  let ws = null;
  let ping = null;
  let remoteAddr = null;
  let remotePort = null;
  let addrToSend = '';
  const aServer = getServer();
  connection.on('data', function(data) {
    if (stage === 5) {
      // pipe sockets
      data = encryptor.encrypt(data);
      if (ws.readyState === WebSocket.OPEN) {
        ws.send(data, { binary: true });
      }
      return;
    }
    if (stage === 0) {
      const tempBuf = new Buffer(2);
      tempBuf.write('\u0005\u0000', 0);
      connection.write(tempBuf);
      stage = 1;
      return;
    }
    if (stage === 1) {
      try {
        // +----+-----+-------+------+----------+----------+
        // |VER | CMD |  RSV  | ATYP | DST.ADDR | DST.PORT |
        // +----+-----+-------+------+----------+----------+
        // | 1  |  1  | X'00' |  1   | Variable |    2     |
        // +----+-----+-------+------+----------+----------+

        //cmd and addrtype
        const cmd = data[1];
        const addrtype = data[3];
        if (cmd !== 1) {
          console.log('unsupported cmd:', cmd);
          const reply = new Buffer('\u0005\u0007\u0000\u0001', 'binary');
          connection.end(reply);
          return;
        }
        if (addrtype === 3) {
          addrLen = data[4];
        } else if (addrtype !== 1) {
          console.log('unsupported addrtype:', addrtype);
          connection.end();
          return;
        }
        addrToSend = data.slice(3, 4).toString('binary');
        // read address and port
        if (addrtype === 1) {
          remoteAddr = inetNtoa(data.slice(4, 8));
          addrToSend += data.slice(4, 10).toString('binary');
          remotePort = data.readUInt16BE(8);
          headerLength = 10;
        } else {
          remoteAddr = data.slice(5, 5 + addrLen).toString('binary');
          addrToSend += data.slice(4, 5 + addrLen + 2).toString('binary');
          remotePort = data.readUInt16BE(5 + addrLen);
          headerLength = 5 + addrLen + 2;
        }
        let buf = new Buffer(10);
        buf.write('\u0005\u0000\u0000\u0001', 0, 4, 'binary');
        buf.write('\u0000\u0000\u0000\u0000', 4, 4, 'binary');
        buf.writeUInt16BE(remotePort, 8);
        connection.write(buf);
        // connect to remote server
        // ws = new WebSocket aServer, protocol: "binary"

        if (HTTPPROXY) {
          // WebSocket endpoint for the proxy to connect to
          const endpoint = aServer;
          const parsed = url.parse(endpoint);
          //console.log('attempting to connect to WebSocket %j', endpoint);

          // create an instance of the `HttpsProxyAgent` class with the proxy server information
          const opts = url.parse(HTTPPROXY);

          // IMPORTANT! Set the `secureEndpoint` option to `false` when connecting
          //            over "ws://", but `true` when connecting over "wss://"
          opts.secureEndpoint = parsed.protocol
            ? parsed.protocol == 'wss:'
            : false;

          const agent = new HttpsProxyAgent(opts);

          ws = new WebSocket(aServer, {
            protocol: 'binary',
            agent
          });
        } else {
          ws = new WebSocket(aServer, {
            protocol: 'binary'
          });
        }

        ws.on('open', function() {
          console.log(`connecting ${remoteAddr} via ${aServer}`);
          let addrToSendBuf = new Buffer(addrToSend, 'binary');
          addrToSendBuf = encryptor.encrypt(addrToSendBuf);
          ws.send(addrToSendBuf, { binary: true });
          let i = 0;

          while (i < cachedPieces.length) {
            let piece = cachedPieces[i];
            piece = encryptor.encrypt(piece);
            ws.send(piece, { binary: true });
            i++;
          }
          cachedPieces = null; // save memory
          stage = 5;

          ping = setInterval(() => ws.ping('', null, true), 50 * 1000);
        });

        ws.on('message', function(data, flags) {
          data = encryptor.decrypt(data);
          connection.write(data);
        });

        ws.on('close', function() {
          clearInterval(ping);
          console.log('remote disconnected');
          connection.destroy();
        });

        ws.on('error', function(e) {
          console.log(`remote ${remoteAddr}:${remotePort} error: ${e}`);
          connection.destroy();
          server.getConnections(function(err, count) {
            console.log('concurrent connections:', count);
          });
        });

        if (data.length > headerLength) {
          buf = new Buffer(data.length - headerLength);
          data.copy(buf, 0, headerLength);
          cachedPieces.push(buf);
          buf = null;
        }
        stage = 4;
      } catch (error) {
        // may encounter index out of range
        const e = error;
        console.log(e);
        connection.destroy();
      }
    } else if (stage === 4) {
      // remote server not connected
      // cache received buffers
      // make sure no data is lost
      cachedPieces.push(data);
    }
  });

  connection.on('end', function() {
    console.log('local disconnected');
    if (ws) {
      ws.terminate();
    }
    server.getConnections(function(err, count) {
      console.log('concurrent connections:', count);
    });
  });

  connection.on('error', function(e) {
    console.log(`local error: ${e}`);
    if (ws) {
      ws.terminate();
    }
    server.getConnections(function(err, count) {
      console.log('concurrent connections:', count);
    });
  });

  connection.setTimeout(timeout, function() {
    console.log('local timeout');
    connection.destroy();
    if (ws) {
      ws.terminate();
    }
  });
});

server.listen(PORT, LOCAL_ADDRESS, function() {
  const address = server.address();
  console.log('server listening at', address);
});

server.on('error', function(e) {
  if (e.code === 'EADDRINUSE') {
    console.log('address in use, aborting');
  }
  process.exit(1);
});
