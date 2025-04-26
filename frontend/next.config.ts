import type { NextConfig } from "next";

const nextConfig: NextConfig = {
  webpack: (config, { isServer }) => {
    if (!isServer) {
      config.resolve.alias['node:child_process'] = false;
      config.resolve.alias['node:fs'] = false;
      config.resolve.alias['node:constants'] = false;
      config.resolve.alias['node:tty'] = false;
    }
    return config;
  },

};

export default nextConfig;
